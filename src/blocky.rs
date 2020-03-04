use datafrog::{Iteration, Relation, RelationLeaper};
use std::time::Instant;

use std::collections::BTreeSet;
use polonius_engine::FactTypes;
use polonius_engine::output::Output;
use rustc_hash::FxHashSet;

/// Subset of `AllFacts` dedicated to borrow checking, and data ready to use by the variants
pub struct Context<'ctx, T: FactTypes> {
    // `Relation`s used as static inputs, by all variants
    pub region_live_at: &'ctx Relation<(T::Origin, T::Point)>,
    pub invalidates: &'ctx Relation<(T::Loan, T::Point)>,

    // static inputs used via `Variable`s, by all variants
    pub outlives: &'ctx FxHashSet<(T::Origin, T::Origin, T::Point)>,
    pub borrow_region: &'ctx FxHashSet<(T::Origin, T::Loan, T::Point)>,

    // static inputs used by variants other than `LocationInsensitive`
    pub cfg_node: &'ctx BTreeSet<T::Point>,
    pub killed: &'ctx Relation<(T::Loan, T::Point)>,

    // pub known_contains: &'ctx Relation<(T::Origin, T::Loan)>,
    pub placeholder_origin: &'ctx Relation<(T::Origin, ())>,
    pub placeholder_loan: &'ctx Relation<(T::Loan, T::Origin)>,

    // while this static input is unused by `LocationInsensitive`, it's depended on by initialization
    // and liveness, so already computed by the time we get to borrowcking.
    pub cfg_edge: &'ctx Relation<(T::Point, T::Point)>,

    pub known_subset: &'ctx Relation<(T::Origin, T::Origin)>,
}

pub struct BlockyResult<T: FactTypes> {
    pub errors: Relation<(T::Loan, T::Point)>,
    pub subset_errors: Relation<(T::Origin, T::Origin, T::Point)>,

    pub subset: Relation<(T::Origin, T::Origin, T::Point)>,
    pub requires: Relation<(T::Origin, T::Loan, T::Point)>,

    pub new_tuples: usize,
}

pub fn compute<T: FactTypes>(
    ctx: &Context<T>,
    _result: &mut Output<T>,
) -> BlockyResult<T> {
    let _timer = Instant::now();
    
    // Static inputs
    
    // function data
    // let known_contains = ctx.known_contains;
    let known_subset = ctx.known_subset;
    let placeholder_origin = ctx.placeholder_origin;
    // let placeholder_loan = ctx.placeholder_loan;

    // block data
    let region_live_at_rel = ctx.region_live_at;
    let cfg_edge_rel = ctx.cfg_edge;
    // let cfg_node = ctx.cfg_node;
    let killed_rel = ctx.killed;
    

    // Create a new iteration context, ...
    let mut iteration = Iteration::new();

    // .. some variables, ..
    let subset = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset");
    let requires = iteration.variable::<(T::Origin, T::Loan, T::Point)>("requires");
    let borrow_live_at = iteration.variable::<((T::Loan, T::Point), ())>("borrow_live_at");

    // `invalidates` facts, stored ready for joins
    let invalidates = iteration.variable::<((T::Loan, T::Point), ())>("invalidates");

    // different indices for `subset`.
    let subset_o1p = iteration.variable_indistinct("subset_o1p");
    let subset_o2p = iteration.variable_indistinct("subset_o2p");

    // different index for `requires`.
    let requires_op = iteration.variable_indistinct("requires_op");

    // we need `region_live_at` in both variable and relation forms.
    // (respectively, for the regular join and the leapjoin).
    let region_live_at_var =
        iteration.variable::<((T::Origin, T::Point), ())>("region_live_at");

    // output relations: illegal accesses errors, and illegal subset relations errors
    let errors = iteration.variable("errors");
    let subset_errors = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset_errors");

    let subset_placeholder = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset_placeholder");
    let subset_placeholder_o2p = iteration.variable_indistinct("subset_placeholder_o2p");

    // load initial facts.
    subset.extend(ctx.outlives.iter());
    requires.extend(ctx.borrow_region.iter());
    invalidates.extend(
        ctx.invalidates
            .iter()
            .map(|&(loan, point)| ((loan, point), ())),
    );

    if !ctx.invalidates.is_empty() {
        region_live_at_var.extend(
            region_live_at_rel
                .iter()
                .map(|&(origin, point)| ((origin, point), ())),
        );
    }

    // // Placeholder loans are contained by their placeholder origin at all points of the CFG.
    // //
    // // contains(Origin, Loan, Node) :-
    // //   cfg_node(Node),
    // //   placeholder(Origin, Loan).
    // let mut placeholder_loans = Vec::with_capacity(placeholder_loan.len() * cfg_node.len());
    // for &(loan, origin) in placeholder_loan.iter() {
    //     for &node in cfg_node.iter() {
    //         placeholder_loans.push((origin, loan, node));
    //     }
    // }

    // let placeholder_loans_count = placeholder_loans.len();
    // requires.extend(placeholder_loans);

    // .. and then start iterating rules!
    while iteration.changed() {
        // Cleanup step: remove symmetries
        // - remove regions which are `subset`s of themselves
        //
        // FIXME: investigate whether is there a better way to do that without complicating
        // the rules too much, because it would also require temporary variables and
        // impact performance. Until then, the big reduction in tuples improves performance
        // a lot, even if we're potentially adding a small number of tuples
        // per round just to remove them in the next round.
        subset
            .recent
            .borrow_mut()
            .elements
            .retain(|&(origin1, origin2, _)| origin1 != origin2);
        subset_placeholder
            .recent
            .borrow_mut()
            .elements
            .retain(|&(origin1, origin2, _)| origin1 != origin2);

        // remap fields to re-index by keys.
        subset_o1p.from_map(&subset, |&(origin1, origin2, point)| {
            ((origin1, point), origin2)
        });
        subset_o2p.from_map(&subset, |&(origin1, origin2, point)| {
            ((origin2, point), origin1)
        });

        subset_placeholder_o2p.from_map(&subset_placeholder, |&(origin1, origin2, point)| {
            ((origin2, point), origin1)
        });

        requires_op.from_map(&requires, |&(origin, loan, point)| ((origin, point), loan));

        // subset(origin1, origin2, point) :- outlives(origin1, origin2, point).
        // Already loaded; outlives is static.

        // subset(origin1, origin3, point) :-
        //   subset(origin1, origin2, point),
        //   subset(origin2, origin3, point).
        subset.from_join(
            &subset_o2p,
            &subset_o1p,
            |&(_origin2, point), &origin1, &origin3| (origin1, origin3, point),
        );

        // subset(origin1, origin2, point2) :-
        //   subset(origin1, origin2, point1),
        //   cfg_edge(point1, point2),
        //   region_live_at(origin1, point2),
        //   region_live_at(origin2, point2).
        subset.from_leapjoin(
            &subset,
            (
                cfg_edge_rel.extend_with(|&(_origin1, _origin2, point1)| point1),
                region_live_at_rel.extend_with(|&(origin1, _origin2, _point1)| origin1),
                region_live_at_rel.extend_with(|&(_origin1, origin2, _point1)| origin2),
            ),
            |&(origin1, origin2, _point1), &point2| (origin1, origin2, point2),
        );

        // requires(origin, loan, point) :- borrow_region(origin, loan, point).
        // Already loaded; borrow_region is static.

        // requires(origin2, loan, point) :-
        //   requires(origin1, loan, point),
        //   subset(origin1, origin2, point).
        requires.from_join(
            &requires_op,
            &subset_o1p,
            |&(_origin1, point), &loan, &origin2| (origin2, loan, point),
        );

        // requires(origin, loan, point2) :-
        //   requires(origin, loan, point1),
        //   !killed(loan, point1),
        //   cfg_edge(point1, point2),
        //   region_live_at(origin, point2).
        requires.from_leapjoin(
            &requires,
            (
                killed_rel.filter_anti(|&(_origin, loan, point1)| (loan, point1)),
                cfg_edge_rel.extend_with(|&(_origin, _loan, point1)| point1),
                region_live_at_rel.extend_with(|&(origin, _loan, _point1)| origin),
            ),
            |&(origin, loan, _point1), &point2| (origin, loan, point2),
        );

        if !ctx.invalidates.is_empty() {
            // borrow_live_at(loan, point) :-
            //   requires(origin, loan, point),
            //   region_live_at(origin, point).
            borrow_live_at.from_join(
                &requires_op,
                &region_live_at_var,
                |&(_origin, point), &loan, _| ((loan, point), ()),
            );
        }

        // errors(loan, point) :-
        //   invalidates(loan, point),
        //   borrow_live_at(loan, point).
        errors.from_join(&invalidates, &borrow_live_at, |&(loan, point), _, _| {
            (loan, point)
        });

        // // subset_errors(Origin1, Origin2, Point) :-
        // //   requires(Origin2, Loan1, Point),
        // //   placeholder(Origin2, _),
        // //   placeholder(Origin1, Loan1),
        // //   !known_contains(Origin2, Loan1).
        // subset_errors.from_leapjoin(
        //     &requires,
        //     (
        //         placeholder_origin.filter_with(|&(origin2, _loan1, _point)| (origin2, ())),
        //         placeholder_loan.extend_with(|&(_origin2, loan1, _point)| loan1),
        //         known_contains.filter_anti(|&(origin2, loan1, _point)| (origin2, loan1)),
        //         // remove symmetries:
        //         datafrog::ValueFilter::from(|&(origin2, _loan1, _point), &origin1| {
        //             origin2 != origin1
        //         }),
        //     ),
        //     |&(origin2, _loan1, point), &origin1| (origin1, origin2, point),
        // );

        // subset_placeholder(Origin1, Origin2, Point) :-
        //     subset(Origin1, Origin2, Point),
        //     placeholder_region(Origin1).
        subset_placeholder.from_leapjoin(
            &subset,
            (
                placeholder_origin.extend_with(|&(origin1, _origin2, _point)| origin1),
                // remove symmetries:
                datafrog::ValueFilter::from(|&(origin1, origin2, _point), ()| {
                    origin2 != origin1
                }),
            ),
            |&(origin1, origin2, point), _| (origin1, origin2, point)
        );

        // subset_placeholder(Origin1, Origin3, Point) :-
        //     subset_placeholder(Origin1, Origin2, Point),
        //     subset(Origin2, Origin3, Point).
        subset_placeholder.from_join(
            &subset_placeholder_o2p,
            &subset_o1p,
            |&(_origin2, point), &origin1, &origin3| (origin1, origin3, point)
        );

        // subset_error(R1, R2, P) :-
        //     subset_placeholder(R1, R2, P),
        //     placeholder_region(R2),
        //     !known_subset(R1, R2).
        subset_errors.from_leapjoin(
            &subset_placeholder,
            (
                placeholder_origin.extend_with(|&(_origin1, origin2, _point)| origin2),
                known_subset.filter_anti(|&(origin1, origin2, _point)| (origin1, origin2)),
                // remove symmetries:
                datafrog::ValueFilter::from(|&(origin1, origin2, _point), ()| {
                    origin2 != origin1
                }),
            ),
            |&(origin1, origin2, point), _| (origin1, origin2, point),
        );
    }

    let (errors, subset_errors) = (errors.complete(), subset_errors.complete());

    // eprintln!(
    //     "analysis done: {} `errors` tuples, {} `subset_errors` tuples, {:?}",
    //     errors.len(),
    //     subset_errors.len(),
    //     timer.elapsed()
    // );

    let (subset, requires) = (subset.complete(), requires.complete());

    // // println!("errors: {}", errors.len());
    // // println!("subset_errors: {}", subset_errors.len());
    // println!("subset: {}", subset.len());
    // println!("subset initial: {}", ctx.outlives.len());
    // // println!("subset initial: {:#?}", ctx.outlives);
    // println!("requires: {}", requires.len());
    // println!("requires initial: {}", ctx.borrow_region.len());
    // println!("placeholder_loans: {}", placeholder_loans_count);

    // let subset_placeholder = subset_placeholder.complete();
    // println!("subset_placeholder: {}", subset_placeholder.len());
    

    // the new tuples are
    // - the number of new subsets (subsets at the end of the computation minus the initial value)
    // - the number of new requires (requires at the end of the computation minus the initial value)
    let new_tuples = subset.len() - ctx.outlives.len()
        + requires.len() - ctx.borrow_region.len();

    // TODO: enlever les placeholder loans ? ils sont dans require mais ne doivent pas compter comme des nouveaux tuples
    // assert!(placeholder_loans_count == 0);

    BlockyResult {
        errors,
        subset_errors,

        subset,
        requires,

        new_tuples,
    }
}
