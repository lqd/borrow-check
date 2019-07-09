//! A version of the Prototype analysis.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::time::Instant;

use crate::output::Output;
use facts::{AllFacts, Atom};

use datafrog::{Iteration, Relation, RelationLeaper};

pub(super) fn compute<Region: Atom, Loan: Atom, Point: Atom>(
    dump_enabled: bool,
    mut all_facts: AllFacts<Region, Loan, Point>,
) -> Output<Region, Loan, Point> {
    let all_points: BTreeSet<Point> = all_facts
        .cfg_edge
        .iter()
        .map(|&(p, _)| p)
        .chain(all_facts.cfg_edge.iter().map(|&(_, q)| q))
        .collect();

    all_facts
        .region_live_at
        .reserve(all_facts.universal_region.len() * all_points.len());
    for &r in &all_facts.universal_region {
        for &p in &all_points {
            all_facts.region_live_at.push((r, p));
        }
    }

    let mut result = Output::new(dump_enabled);

    let computation_start = Instant::now();

    // 1 - compute subsets TC
    let subsets = {
        let mut iteration = Iteration::new();

        let subset = iteration.variable::<(Region, Region, Point)>("subset");

        let subset_base = Relation::from_iter(
            all_facts.outlives.iter()
                .filter(|&(r1, r2, _)| r1 != r2)
                .map(|(r1, r2, p)| ((*r1, *p), *r2))
        );

        let subset_r1p = iteration.variable_indistinct("subset_r1p");
        // let subset_r2p = iteration.variable_indistinct("subset_r2p");

        // subset(R1, R2, P) :- outlives(R1, R2, P).
        subset.extend(
            all_facts.outlives
                .iter()
                .filter(|&(r1, r2, _)| r1 != r2)
        );

        while iteration.changed() {
            // Cleanup step: remove symmetries
            // - remove regions which are `subset`s of themselves
            //
            // FIXME: investigate whether is there a better way to do that without complicating
            // the rules too much, because it would also require temporary variables and
            // impact performance. Until then, the big reduction in tuples improves performance
            // a lot, even if we're potentially adding a small number of tuples
            // per round just to remove them in the next round.
            // subset
            //     .recent
            //     .borrow_mut()
            //     .elements
            //     .retain(|&(r1, r2, _)| r1 != r2);

            // remap fields to re-index by keys.
            subset_r1p.from_map(&subset, |&(r1, r2, p)| ((r1, p), r2));
            // subset_r2p.from_map(&subset, |&(r1, r2, p)| ((r2, p), r1));

            // subset(R1, R3, P) :-
            //   subset(R1, R2, P),
            //   subset_base(R2, R3, P).
            // subset.from_join(&subset_r2p, &subset_r1p, |&(_r2, p), &r1, &r3| (r1, r3, p));
            subset.from_leapjoin(
                &subset_r1p,
                (
                    subset_base.extend_with(|&((_r1, p), r2)| (r2, p)),
                    datafrog::ValueFilter::from(|&((r1, _p), _r2), &r3| r1 != r3),
                ),
                |&((r1, p), _r2), &r3| (r1, r3, p),
            );
        }

        subset.complete()
    };
    debug_assert_eq!(subsets.iter().filter(|&(r1, r2, _)| r1 == r2).count(), 0);

    println!("subsets relation computed: {} tuples", subsets.elements.len());
    // println!("subsets: {:#?}", subsets.elements);


    // 2 - compute region equality
    let equals = {
        let sets: HashSet<_> = subsets.iter().collect();
        Relation::from_iter(
            subsets
                .iter()
                .filter(|(r1, r2, p)| sets.contains(&(*r2, *r1, *p)))
                .map(|&(r1, r2, p)| ((r1, p), r2))
        )

        // let sets: HashSet<_> = subsets.iter().map(|&(r1, r2, _)| (r1, r2)).collect();
        // Relation::from_iter(
        //     subsets
        //         .iter()
        //         .filter(|(r1, r2, _)| sets.contains(&(*r2, *r1)))
        //         .map(|&(r1, r2, _)| (r1, r2))
        // )
    };
    debug_assert_eq!(equals.iter().filter(|&((r1, _p), r2)| r1 == r2).count(), 0);

    println!("equals relation computed: {} tuples", equals.elements.len());
    // println!("equals: {:?}", equals.elements);

    // 3 - compute provenance information and check illegal accesses
    let errors = {
        // Create a new iteration context, ...
        let mut iteration = Iteration::new();

        // static inputs
        // let subset = iteration.variable_indistinct::<(Region, Region, Point)>("subset");
        // subset.insert(subsets);
        let subsets = Relation::from_iter(subsets.iter().map(|&(r1, r2, p)| ((r1, p), r2)));

        // let equal = iteration.variable_indistinct("equal");
        let equal = iteration.variable("equal");
        equal.insert(equals);

        let cfg_edge_rel: Relation<(Point, Point)> = all_facts.cfg_edge.into();
        let killed_rel: Relation<(Loan, Point)> = all_facts.killed.into();

        // .. some variables, ..
        let requires = iteration.variable::<(Region, Loan, Point)>("requires");
        let borrow_live_at = iteration.variable::<((Loan, Point), ())>("borrow_live_at");

        // `invalidates` facts, stored ready for joins
        let invalidates = iteration.variable_indistinct::<((Loan, Point), ())>("invalidates");
        invalidates.extend(all_facts.invalidates.iter().map(|&(p, b)| ((b, p), ())));

        let invalidates_set = all_facts.invalidates.iter().map(|&(_p, l)| l).collect::<std::collections::HashSet<_>>();

        // different indices for `subset`.
        // let subset_r1p = iteration.variable_indistinct("subset_r1p");

        // different index for `requires`.
        let requires_rp = iteration.variable_indistinct("requires_rp");
        // let requires_r = iteration.variable_indistinct("requires_r");

        // we need `region_live_at` in both variable and relation forms.
        // (respectively, for the regular join and the leapjoin).
        let region_live_at_var = iteration.variable_indistinct::<((Region, Point), ())>("region_live_at");
        let region_live_at_rel = Relation::from_iter(all_facts.region_live_at.iter().cloned());

        region_live_at_var.extend(all_facts.region_live_at.iter().map(|&(r, p)| ((r, p), ())));

        // output
        let errors = iteration.variable("errors");

        // requires(R, L, P) :- borrow_region(R, L, P).
        // requires.insert(all_facts.borrow_region.into());
        requires.insert(
            Relation::from_iter(
                all_facts
                    .borrow_region
                    .into_iter()
                    .filter(|&(_r, l, _p)| invalidates_set.contains(&l)) // new
            )
        );

        while iteration.changed() {
            // subset
            //     .recent
            //     .borrow_mut()
            //     .elements
            //     .retain(|&(r1, r2, _)| r1 != r2);

            // remap fields to re-index by keys.
            // subset_r1p.from_map(&subset, |&(r1, r2, p)| ((r1, p), r2));
            requires_rp.from_map(&requires, |&(r, b, p)| ((r, p), b));
            // requires_r.from_map(&requires, |&(r, b, p)| (r, (b, p)));

            // requires(R2, L, P) :-
            //   requires(R1, L, P),
            //   subset(R1, R2, P).
            // requires.from_join(&requires_rp, &subset_r1p, |&(_r1, p), &l, &r2| (r2, l, p));
            requires.from_leapjoin(
                &requires,
                (
                    subsets.extend_with(|&(r, _l, p)| (r, p)),
                ),
                |&(_r1, l, p), &r2| (r2, l, p),
            );

            // original prototype rule, static equality
            // // requires(R2, L, P) :-
            // //   requires(R1, L, P),
            // //   equals(R1, R2)
            // // requires.from_join(&requires_r, &equal, |&_r2, &(l, p), &r1| (r1, l, p));
            // requires.from_leapjoin(
            //     &requires,
            //     (
            //         equals.extend_with(|&(r, _l, _p)| r),
            //     ),
            //     |&(_r1, l, p), &r2| (r2, l, p),
            // );

            // flow sensitive equality
            // requires(R2, L, P) :-
            //   requires(R1, L, P),
            //   equals(R1, R2, P).
            requires.from_join(&requires_rp, &equal, |&(_r1, p), &l, &r2| (r2, l, p));

            // equals(R1, R2, Q) :-
            //   equals(R1, R2, P),
            //   cfg_edge(P, Q),
            //   region_live_at(R1, Q), ?
            //   region_live_at(R2, Q). ?
            equal.from_leapjoin(
                &equal,
                (
                    cfg_edge_rel.extend_with(|&((_r1, p), _r2)| p),
                    region_live_at_rel.extend_with(|&((r1, _p), _r2)| r1),
                    region_live_at_rel.extend_with(|&((_r1, _p), r2)| r2),
                    // datafrog::ValueFilter::from(|&((r1, _p), r2), &_q| r1 != r2),
                ),
                |&((r1, _p), r2), &q| ((r1, q), r2),
            );

            // requires(R, B, Q) :-
            //   requires(R, B, P),
            //   !killed(B, P),
            //   cfg_edge(P, Q),
            //   region_live_at(R, Q).
            requires.from_leapjoin(
                &requires,
                (
                    killed_rel.filter_anti(|&(_r, b, p)| (b, p)),
                    cfg_edge_rel.extend_with(|&(_r, _b, p)| p),
                    region_live_at_rel.extend_with(|&(r, _b, _p)| r),
                ),
                |&(r, b, _p), &q| (r, b, q),
            );

            // borrow_live_at(B, P) :-
            //   requires(R, B, P),
            //   region_live_at(R, P).
            borrow_live_at.from_join(&requires_rp, &region_live_at_var, |&(_r, p), &b, &()| {
                ((b, p), ())
            });

            // todo: filtering the `borrow_regions` input might make this join unnecessary ?
            // errors(B, P) :-
            //   invalidates(B, P),
            //   borrow_live_at(B, P).
            errors.from_join(&invalidates, &borrow_live_at, |&(b, p), &(), &()| (b, p));
        }

        if dump_enabled {
            // let subset = subset.complete();
            assert!(
                subsets.iter().filter(|&((r1, _p), r2)| r1 == r2).count() == 0,
                "unwanted subset symmetries"
            );
            for ((r1, location), r2) in subsets.iter() {
                result
                    .subset
                    .entry(*location)
                    .or_insert(BTreeMap::new())
                    .entry(*r1)
                    .or_insert(BTreeSet::new())
                    .insert(*r2);
            }

            let requires = requires.complete();
            for (region, borrow, location) in &requires.elements {
                result
                    .restricts
                    .entry(*location)
                    .or_insert(BTreeMap::new())
                    .entry(*region)
                    .or_insert(BTreeSet::new())
                    .insert(*borrow);
            }

            for (region, location) in &region_live_at_rel.elements {
                result
                    .region_live_at
                    .entry(*location)
                    .or_insert(vec![])
                    .push(*region);
            }

            let borrow_live_at = borrow_live_at.complete();
            for &((loan, location), ()) in &borrow_live_at.elements {
                result
                    .borrow_live_at
                    .entry(location)
                    .or_insert(Vec::new())
                    .push(loan);
            }
        }

        errors.complete()
    };

    if dump_enabled {
        info!(
            "errors is complete: {} tuples, {:?}",
            errors.len(),
            computation_start.elapsed()
        );
    }

    for (borrow, location) in &errors.elements {
        result
            .errors
            .entry(*location)
            .or_insert(Vec::new())
            .push(*borrow);
    }

    result
}
