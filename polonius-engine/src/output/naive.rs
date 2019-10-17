// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A version of the Naive datalog analysis using Datafrog.

use datafrog::{Iteration, Relation, RelationLeaper};
use std::time::Instant;

use crate::facts::FactTypes;
use crate::output::{Context, Output};

pub(super) fn compute<T: FactTypes>(
    ctx: &Context<T>,
    result: &mut Output<T>,
) -> Relation<(T::Loan, T::Point)> {
    let timer = Instant::now();

    let errors = {
        let all_facts = &ctx.all_facts;

        // Static inputs
        let region_live_at_rel = &ctx.region_live_at;
        let cfg_edge_rel = &ctx.cfg_edge;
        let killed_rel = &ctx.killed;

        let placeholder_origin: Relation<(T::Origin, T::Loan)> = all_facts.placeholder_origin.clone().into();
        let placeholder_origin_l: Relation<_> = Relation::from_iter(
            placeholder_origin.iter().map(|&(origin, loan)| (loan, origin))
        );
        let known_subset: Relation<(T::Origin, T::Origin)> = all_facts.known_subset.clone().into();

        // Create a new iteration context, ...
        let mut iteration = Iteration::new();

        // .. some variables, ..
        let subset = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset");
        let requires = iteration.variable::<(T::Origin, T::Loan, T::Point)>("requires");

        // Note: `requires_o` is an indexed version of the `requires` relation
        let requires_o = iteration.variable_indistinct::<(T::Origin, (T::Loan, T::Point))>("requires_o");

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

        // output
        let errors = iteration.variable("errors");
        
        let subset_errors = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset_errors");
        let subset_errors_step_9_1 = iteration.variable("subset_errors_step_9_1");
        let subset_errors_step_9_2 = iteration.variable("subset_errors_step_9_2");

        // load initial facts.
        subset.extend(all_facts.outlives.iter());
        requires.extend(all_facts.borrow_region.iter());
        invalidates.extend(
            all_facts
                .invalidates
                .iter()
                .map(|&(point, loan)| ((loan, point), ())),
        );
        region_live_at_var.extend(
            region_live_at_rel
                .iter()
                .map(|&(origin, point)| ((origin, point), ())),
        );

        // seed placeholder loans into requires at the start of the cfg
        let cfg_start = cfg_edge_rel.iter().next().unwrap().0;
        requires.extend(placeholder_origin.iter().map(|&(origin, loan)| (origin, loan, cfg_start)));

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

            // remap fields to re-index by keys.
            subset_o1p.from_map(&subset, |&(origin1, origin2, point)| {
                ((origin1, point), origin2)
            });
            subset_o2p.from_map(&subset, |&(origin1, origin2, point)| {
                ((origin2, point), origin1)
            });

            requires_op.from_map(&requires, |&(origin, loan, point)| ((origin, point), loan));
            requires_o.from_map(&requires, |&(origin, loan, point)| (origin, (loan, point)));

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

            // borrow_live_at(loan, point) :-
            //   requires(origin, loan, point),
            //   region_live_at(origin, point).
            borrow_live_at.from_join(
                &requires_op,
                &region_live_at_var,
                |&(_origin, point), &loan, _| ((loan, point), ()),
            );

            // errors(loan, point) :-
            //   invalidates(loan, point),
            //   borrow_live_at(loan, point).
            errors.from_join(&invalidates, &borrow_live_at, |&(loan, point), _, _| {
                (loan, point)
            });

            // subset_error(origin1, origin2, point) :-
            //   requires(origin2, loan1, point),
            //   placeholder_origin(origin2, _),
            //   placeholder_origin(origin1, loan1), // placeholder region O1 has associated loan `loan1`
            //   !known_subset(origin1, origin2).
            // subset_errors.from_leapjoin(
            //     &requires,
            //     (
            //         placeholder_origin.extend_with(|&(origin2, loan1, point)| origin2),
            //         placeholder_origin_lo.extend_with(|&(_origin2, loan1, _point)| loan1),
            //         // datafrog::ValueFilter::from(|&(origin2, loan1, point), &origin1| true),
            //     ),
            //     |&(origin2, loan1, point), &origin1| (origin1, origin2, point)
            // );

            // R09: subset_error(O1, O2, P) :- 
            //        requires(O2, L, P), 
            //        placeholder_origin(O2, _), 
            //        placeholder_origin(O1, L), 
            //        !known_subset(O1, O2).
            // TODO: integrate a filter on O1 != O2 in the leapjoin
            // TODO: eliminate requires_o: rename step9_1 to placeholder_origin_requires (avec une leapjoin par ex, mais
            // vérifier si l'economie de l'index vaut bien le coup de la leapjoin à 2 predicats)
            // - réussir à faire une leapjoin serait une autre solution...
            subset_errors_step_9_1.from_join(&requires_o, &placeholder_origin, |&o2, &(l, p), _| (l, (o2, p)));
            subset_errors_step_9_2.from_join(&subset_errors_step_9_1, &placeholder_origin_l, |&_l, &(o2, p), &o1| ((o1, o2), p));
            subset_errors.from_antijoin(&subset_errors_step_9_2, &known_subset, |&(o1, o2), &p| (o1, o2, p));

            subset_errors
                .recent
                .borrow_mut()
                .elements
                .retain(|&(origin1, origin2, _)| origin1 != origin2);
        }

        if result.dump_enabled {
            let subset = subset.complete();
            assert!(
                subset
                    .iter()
                    .filter(|&(origin1, origin2, _)| origin1 == origin2)
                    .count()
                    == 0,
                "unwanted subset symmetries"
            );
            for &(origin1, origin2, location) in subset.iter() {
                result
                    .subset
                    .entry(location)
                    .or_default()
                    .entry(origin1)
                    .or_default()
                    .insert(origin2);
            }

            let requires = requires.complete();
            for &(origin, loan, location) in requires.iter() {
                result
                    .restricts
                    .entry(location)
                    .or_default()
                    .entry(origin)
                    .or_default()
                    .insert(loan);
            }

            let borrow_live_at = borrow_live_at.complete();
            for &((loan, location), _) in borrow_live_at.iter() {
                result
                    .borrow_live_at
                    .entry(location)
                    .or_default()
                    .push(loan);
            }
        }

        let subset_errors = subset_errors.complete();
        for &(origin1, origin2, location) in subset_errors.iter() {
            result.subset_errors.entry(location).or_default().insert((origin1, origin2));
        }

        errors.complete()
    };

    info!(
        "errors is complete: {} tuples, {:?}",
        errors.len(),
        timer.elapsed()
    );

    errors
}
