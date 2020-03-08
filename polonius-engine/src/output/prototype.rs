//! A version of the Prototype analysis.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use crate::output::initialization;
use crate::output::liveness;
use crate::output::Output;
use facts::{AllFacts, Atom};

use datafrog::{Iteration, Relation, RelationLeaper};
use rustc_hash::FxHashSet;

pub(super) fn compute<Origin: Atom, Loan: Atom, Point: Atom, Variable: Atom, MovePath: Atom>(
    dump_enabled: bool,
    all_facts: AllFacts<Origin, Loan, Point, Variable, MovePath>,
) -> Output<Origin, Loan, Point, Variable, MovePath> {
    let mut result = Output::new(dump_enabled);

    let var_maybe_initialized_on_exit = initialization::init_var_maybe_initialized_on_exit(
        all_facts.child,
        all_facts.path_belongs_to_var,
        all_facts.initialized_at,
        all_facts.moved_out_at,
        all_facts.path_accessed_at,
        &all_facts.cfg_edge,
        &mut result,
    );

    let region_live_at = liveness::init_region_live_at(
        all_facts.var_used,
        all_facts.var_drop_used,
        all_facts.var_defined,
        all_facts.var_uses_region,
        all_facts.var_drops_region,
        var_maybe_initialized_on_exit,
        &all_facts.cfg_edge,
        all_facts.universal_region,
        &mut result,
    );

    // The set of "interesting" loans
    let invalidates_set: FxHashSet<_> = all_facts.invalidates.iter().map(|&(_p, l)| l).collect();

    // The "interesting" borrow regions are the ones referring to loans for which an error could occur
    let interesting_borrow_region: Relation<(Origin, Loan, Point)> = all_facts
        .borrow_region
        .iter()
        .filter(|&(_o, l, _p)| invalidates_set.contains(l))
        .collect();

    // The interesting regions are any region into which an interesting loan could flow
    let interesting_region = {
        let mut iteration = Iteration::new();

        let outlives_o1 =
            Relation::from_iter(all_facts.outlives.iter().map(|&(o1, o2, _p)| (o1, o2)));

        let interesting_region = iteration.variable::<(Origin, ())>("interesting_region");

        // interesting_region(O) :- interesting_borrow_region(O, _, _);
        interesting_region.extend(interesting_borrow_region.iter().map(|&(o, _l, _p)| (o, ())));

        while iteration.changed() {
            // interesting_region(O2) :-
            //     outlives(O1, O2, _),
            //     interesting_region(O1, _, _);
            interesting_region
                .from_join(&interesting_region, &outlives_o1, |_o1, (), &o2| (o2, ()));
        }

        interesting_region
            .complete()
            .iter()
            .map(|&(o1, _)| o1)
            .collect::<FxHashSet<_>>()
    };

    // Limit the `subset` relation to interesting regions
    let interesting_outlives = all_facts
        .outlives
        .iter()
        .filter(|&(o1, _o2, _p)| interesting_region.contains(o1));

    // Extensional predicates, and their indices

    let cfg_edge: Relation<(Point, Point)> = all_facts.cfg_edge.into();
    let invalidates: Relation<((Loan, Point), ())> =
        Relation::from_iter(all_facts.invalidates.iter().map(|&(p, l)| ((l, p), ())));
    let killed: Relation<(Loan, Point)> = all_facts.killed.into();

    // Note: `outlives_o1p` is an indexed version of the input facts `outlives`
    let outlives_o1p: Relation<((Origin, Point), Origin)> =
        Relation::from_iter(interesting_outlives.map(|&(o1, o2, p)| ((o1, p), o2)));

    let region_live_at: Relation<(Origin, Point)> = region_live_at.into();

    let computation_start = Instant::now();

    // `errors` inferred as the output relation
    let errors = {
        let mut iteration = Iteration::new();

        // Intensional predicates, and their indices

        let borrow_live_at = iteration.variable::<((Loan, Point), ())>("borrow_live_at");

        // Note: `equals_o1p` is an indexed version of the `equals` relation
        let equals_o1p = iteration.variable::<((Origin, Point), Origin)>("equals_o1p");

        // Note: `equals_o2p` is an indexed version of the `equals` relation
        let equals_o2p = iteration.variable::<((Origin, Point), Origin)>("equals_o2p");

        // Note: `requires_op` is an indexed version of the `requires` relation
        let requires_op = iteration.variable::<((Origin, Point), Loan)>("requires_op");
        let subset = iteration.variable::<((Origin, Origin, Point), ())>("subset");

        // Note: `subset_o1p` is an indexed version of the `subset` relation
        let subset_o1p = iteration.variable::<((Origin, Point), Origin)>("subset_o1p");

        // Note: `subset_o2o1p` is an indexed version of the `subset` relation
        let subset_o2o1p = iteration.variable::<((Origin, Origin, Point), ())>("subset_o2o1p");

        // Note: `subset_o2p` is an indexed version of the `subset` relation
        let subset_o2p = iteration.variable::<((Origin, Point), Origin)>("subset_o2p");

        // we need `region_live_at` in both variable and relation forms.
        // (respectively, wrapped for the regular join, and for the leapjoin).
        let region_live_at_var = iteration.variable::<((Origin, Point), ())>("region_live_at");
        region_live_at_var.extend(region_live_at.iter().map(|&(o, p)| ((o, p), ())));

        // output relation
        let errors = iteration.variable::<(Loan, Point)>("errors");

        // Load static input data

        // R01: subset(O1, O2, P) :- outlives(O1, O2, P).
        subset.extend(outlives_o1p.iter().map(|&((o1, p), o2)| ((o1, o2, p), ())));

        // R07: requires(O, L, P) :- borrow_region(O, L, P).
        requires_op.extend(
            interesting_borrow_region
                .iter()
                .map(|&(o, l, p)| ((o, p), l)),
        );

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
        }

        if dump_enabled {
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

            for (origin, point) in &region_live_at.elements {
                result
                    .region_live_at
                    .entry(*point)
                    .or_insert(vec![])
                    .push(*origin);
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

        errors.complete()
    };

    if dump_enabled {
        info!(
            "errors is complete: {} tuples, {:?}",
            errors.len(),
            computation_start.elapsed()
        );
    }

    for (loan, point) in &errors.elements {
        result
            .errors
            .entry(*point)
            .or_insert(Vec::new())
            .push(*loan);
    }

    result
}
