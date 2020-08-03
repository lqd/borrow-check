//! A version of the prototype Equality analysis.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use crate::facts::FactTypes;
use crate::output::{Context, Output};

use datafrog::{Iteration, Relation, RelationLeaper};

pub(super) fn compute<T: FactTypes>(
    ctx: &Context<'_, T>,
    result: &mut Output<T>,
) -> (
    Relation<(T::Loan, T::Point)>,
    Relation<(T::Origin, T::Origin, T::Point)>,
) {
    let timer = Instant::now();

    // Extensional predicates, and their indices

    let cfg_edge = &ctx.cfg_edge;
    let invalidates: Relation<((T::Loan, T::Point), ())> =
        Relation::from_iter(ctx.invalidates.iter().map(|&(l, p)| ((l, p), ())));
    let killed = &ctx.killed;

    let known_contains = &ctx.known_contains;
    let placeholder_origin = &ctx.placeholder_origin;
    let placeholder_loan = &ctx.placeholder_loan;
    let cfg_node = ctx.cfg_node;

    // Note: `outlives_o1p` is an indexed version of the input facts `outlives`
    let outlives_o1p: Relation<((T::Origin, T::Point), T::Origin)> =
        Relation::from_iter(ctx.outlives.iter().map(|&(o1, o2, p)| ((o1, p), o2)));

    let region_live_at = &ctx.origin_live_on_entry;

    // `errors` inferred as the output relation
    let (errors, subset_errors) = {
        let mut iteration = Iteration::new();

        // Intensional predicates, and their indices

        let borrow_live_at = iteration.variable::<((T::Loan, T::Point), ())>("borrow_live_at");

        // Note: `equals_o1p` is an indexed version of the `equals` relation
        let equals_o1p = iteration.variable::<((T::Origin, T::Point), T::Origin)>("equals_o1p");

        // Note: `equals_o2p` is an indexed version of the `equals` relation
        let equals_o2p = iteration.variable::<((T::Origin, T::Point), T::Origin)>("equals_o2p");

        // Note: `requires_op` is an indexed version of the `requires` relation
        let requires_op = iteration.variable::<((T::Origin, T::Point), T::Loan)>("requires_op");
        let subset = iteration.variable::<((T::Origin, T::Origin, T::Point), ())>("subset");

        // Note: `subset_o1p` is an indexed version of the `subset` relation
        let subset_o1p = iteration.variable::<((T::Origin, T::Point), T::Origin)>("subset_o1p");

        // Note: `subset_o2o1p` is an indexed version of the `subset` relation
        let subset_o2o1p =
            iteration.variable::<((T::Origin, T::Origin, T::Point), ())>("subset_o2o1p");

        // Note: `subset_o2p` is an indexed version of the `subset` relation
        let subset_o2p = iteration.variable::<((T::Origin, T::Point), T::Origin)>("subset_o2p");

        // we need `region_live_at` in both variable and relation forms.
        // (respectively, wrapped for the regular join, and for the leapjoin).
        let region_live_at_var =
            iteration.variable::<((T::Origin, T::Point), ())>("region_live_at");
        region_live_at_var.extend(region_live_at.iter().map(|&(o, p)| ((o, p), ())));

        // output relation
        let errors = iteration.variable::<(T::Loan, T::Point)>("errors");
        let subset_errors = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset_errors");

        // Load static input data

        // R01: subset(O1, O2, P) :- outlives(O1, O2, P).
        subset.extend(outlives_o1p.iter().map(|&((o1, p), o2)| ((o1, o2, p), ())));

        // R07: requires(O, L, P) :- borrow_region(O, L, P).
        requires_op.extend(ctx.borrow_region.iter().map(|&(o, l, p)| ((o, p), l)));

        // Placeholder loans are contained by their placeholder origin at all points of the CFG.
        //
        // contains(Origin, Loan, Node) :-
        //   cfg_node(Node),
        //   placeholder(Origin, Loan).
        let mut placeholder_loans = Vec::with_capacity(placeholder_loan.len() * cfg_node.len());
        for &(loan, origin) in placeholder_loan.iter() {
            for &node in cfg_node.iter() {
                placeholder_loans.push(((origin, node), loan));
            }
        }

        requires_op.extend(placeholder_loans);

        while iteration.changed() {
            equals_o1p
                .recent
                .borrow_mut()
                .elements
                .retain(|&((o1, _), o2)| o1 != o2);
            subset
                .recent
                .borrow_mut()
                .elements
                .retain(|&((o1, o2, _), _)| o1 != o2);

            // Index maintenance
            equals_o2p.from_map(&equals_o1p, |&((o1, p), o2)| ((o2, p), o1));
            subset_o1p.from_map(&subset, |&((o1, o2, p), _)| ((o1, p), o2));
            subset_o2p.from_map(&subset, |&((o1, o2, p), _)| ((o2, p), o1));
            subset_o2o1p.from_map(&subset, |&((o1, o2, p), _)| ((o2, o1, p), ()));

            // Rules

            // R01: subset(O1, O2, P) :-
            //        outlives(O1, O2, P).
            // `outlives` is a static input, already loaded into `subset`.

            // R02: subset(O1, O3, P) :-
            //        subset(O1, O2, P),
            //        outlives(O2, O3, P).
            subset.from_join(&subset_o2p, &outlives_o1p, |&(_o2, p), &o1, &o3| {
                ((o1, o3, p), ())
            });

            // R03: equals(O1, O2, P) :-
            //        subset(O1, O2, P),
            //        subset(O2, O1, P).
            equals_o1p.from_join(&subset, &subset_o2o1p, |&(o1, o2, p), _, _| ((o1, p), o2));

            // R04: equals(O1, O3, P) :-
            //        equals(O1, O2, P),
            //        equals(O2, O3, P).
            equals_o1p.from_join(&equals_o2p, &equals_o1p, |&(_o2, p), &o1, &o3| {
                ((o1, p), o3)
            });

            // R05: equals(O1, O2, Q) :-
            //        equals(O1, O2, P),
            //        cfg_edge(P, Q),
            //        region_live_at(O1, Q),
            //        region_live_at(O2, Q).
            equals_o1p.from_leapjoin(
                &equals_o1p,
                (
                    cfg_edge.extend_with(|&((_o1, p), _o2)| p),
                    region_live_at.extend_with(|&((o1, _p), _o2)| o1),
                    region_live_at.extend_with(|&((_o1, _p), o2)| o2),
                ),
                |&((o1, _p), o2), &q| ((o1, q), o2),
            );

            // R06: requires(O2, L, P) :-
            //        requires(O1, L, P),
            //        equals(O1, O2, P).
            requires_op.from_join(&requires_op, &equals_o1p, |&(_o1, p), &l, &o2| ((o2, p), l));

            // R07: requires(O, L, P) :-
            //        borrow_region(O, L, P).
            // `borrow_region` is a static input, already loaded into `requires`.

            // R08: requires(O2, L, P) :-
            //        requires(O1, L, P),
            //        subset(O1, O2, P).
            requires_op.from_join(&requires_op, &subset_o1p, |&(_o1, p), &l, &o2| ((o2, p), l));

            // R09: requires(O, L, Q) :-
            //        requires(O, L, P),
            //        !killed(L, P),
            //        cfg_edge(P, Q),
            //        region_live_at(O, Q).
            requires_op.from_leapjoin(
                &requires_op,
                (
                    killed.filter_anti(|&((_o, p), l)| (l, p)),
                    cfg_edge.extend_with(|&((_o, p), _)| p),
                    region_live_at.extend_with(|&((o, _p), _l)| o),
                ),
                |&((o, _p), l), &q| ((o, q), l),
            );

            // R10: borrow_live_at(L, P) :-
            //        requires(O, L, P),
            //        region_live_at(O, P).
            borrow_live_at.from_join(&requires_op, &region_live_at_var, |&(_o, p), &l, _| {
                ((l, p), ())
            });

            // R11: errors(L, P) :-
            //        borrow_live_at(L, P),
            //        invalidates(L, P).
            errors.from_join(&borrow_live_at, &invalidates, |&(l, p), _, _| (l, p));

            // subset_errors(Origin1, Origin2, Point) :-
            //   requires(Origin2, Loan1, Point),
            //   placeholder(Origin2, _),
            //   placeholder(Origin1, Loan1),
            //   !known_contains(Origin2, Loan1).
            subset_errors.from_leapjoin(
                &requires_op,
                (
                    placeholder_origin.filter_with(|&((origin2, _point), _loan1)| (origin2, ())),
                    placeholder_loan.extend_with(|&((_origin2, _point), loan1)| loan1),
                    known_contains.filter_anti(|&((origin2, _point), loan1)| (origin2, loan1)),
                    // remove symmetries:
                    datafrog::ValueFilter::from(|&((origin2, _point), _loan1), &origin1| {
                        origin2 != origin1
                    }),
                ),
                |&((origin2, point), _loan1), &origin1| (origin1, origin2, point),
            );
        }

        if result.dump_enabled {
            let subset_o1p = subset_o1p.complete();
            assert!(
                subset_o1p.iter().filter(|&((o1, _p), o2)| o1 == o2).count() == 0,
                "unwanted subset symmetries"
            );
            for ((o1, point), o2) in subset_o1p.iter() {
                result
                    .subset
                    .entry(*point)
                    .or_insert(BTreeMap::new())
                    .entry(*o1)
                    .or_insert(BTreeSet::new())
                    .insert(*o2);
            }

            let requires_op = requires_op.complete();
            for ((origin, point), loan) in &requires_op.elements {
                result
                    .restricts
                    .entry(*point)
                    .or_insert(BTreeMap::new())
                    .entry(*origin)
                    .or_insert(BTreeSet::new())
                    .insert(*loan);
            }

            let borrow_live_at = borrow_live_at.complete();
            for &((loan, point), ()) in &borrow_live_at.elements {
                result
                    .borrow_live_at
                    .entry(point)
                    .or_insert(Vec::new())
                    .push(loan);
            }
        }

        (errors.complete(), subset_errors.complete())
    };

    info!(
        "prototype analysis done: {} `errors` tuples, {} `subset_errors` tuples, {:?}",
        errors.len(),
        subset_errors.len(),
        timer.elapsed()
    );

    (errors, subset_errors)
}
