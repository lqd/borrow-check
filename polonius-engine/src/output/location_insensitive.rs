// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use datafrog::{Iteration, Relation, RelationLeaper};
use std::time::Instant;

use crate::facts::FactTypes;
use crate::output::{Context, Output};

pub(super) fn compute<T: FactTypes>(
    ctx: &Context<T>,
    result: &mut Output<T>,
) -> Relation<(T::Loan, T::Point)> {
    let timer = Instant::now();

    let potential_errors = {
        // Static inputs
        let region_live_at = &ctx.region_live_at;
        let invalidates = &ctx.invalidates;
        let placeholder_origin = &ctx.placeholder_origin;
        // let known_subset = &ctx.known_subset;
        let placeholder_loan = &ctx.placeholder_loan;
        let known_contains = &ctx.known_contains;

        // // subset(origin1, origin2) :- outlives(origin1, origin2, _point)
        // let subset = Relation::from_iter(
        //     ctx.outlives
        //         .iter()
        //         .map(|&(origin1, origin2, _point)| (origin1, origin2))
        // );

        // Create a new iteration context, ...
        let mut iteration = Iteration::new();

        // .. some variables, ..
        let subset = iteration.variable::<(T::Origin, T::Origin)>("subset");
        let requires = iteration.variable::<(T::Origin, T::Loan)>("requires");

        // let subset_placeholder = iteration.variable::<(T::Origin, T::Origin)>("subset_placeholder");
        // let subset_placeholder_o2 = iteration.variable_indistinct("subset_placeholder_o2");

        let potential_errors = iteration.variable::<(T::Loan, T::Point)>("potential_errors");
        let potential_subset_errors =
            iteration.variable::<(T::Origin, T::Origin)>("potential_subset_errors");

        // load initial facts.

        // subset(origin1, origin2) :- outlives(origin1, origin2, _point)
        subset.extend(
            ctx.outlives
                .iter()
                .map(|&(origin1, origin2, _point)| (origin1, origin2)),
        );

        // requires(origin, loan) :- borrow_region(origin, loan, _point).
        requires.extend(
            ctx.borrow_region
                .iter()
                .map(|&(origin, loan, _point)| (origin, loan)),
        );

        // requires(origin, loan) :-
        //  placeholder_loan(origin, loan).
        requires.extend(placeholder_loan.iter().map(|&(loan, origin)| (origin, loan)));

        // .. and then start iterating rules!
        while iteration.changed() {
            // subset_placeholder
            //     .recent
            //     .borrow_mut()
            //     .elements
            //     .retain(|&(origin1, origin2)| origin1 != origin2);

            // subset_placeholder_o2.from_map(&subset_placeholder, |&(origin1, origin2)| {
            //     (origin2, origin1)
            // });

            // requires(origin2, loan) :-
            //   requires(origin1, loan),
            //   subset(origin1, origin2).
            //
            // Note: Since `subset` is effectively a static input, this join can be ported to
            // a leapjoin. Doing so, however, was 7% slower on `clap`.
            requires.from_join(&requires, &subset, |&_origin1, &loan, &origin2| {
                (origin2, loan)
            });

            // // this is static: push it up outside the loop and just add the subsets of the placeholder
            // // subset_placeholder(Origin1, Origin2) :-
            // //   subset(Origin1, Origin2),
            // //   placeholder_origin(Origin1).
            // subset_placeholder.from_join(&subset, placeholder_origin, |&origin1, &origin2, _| (origin1, origin2));

            // // subset_placeholder(Origin1, Origin3) :-
            // //   subset_placeholder(Origin1, Origin2),
            // //   subset(Origin2, Origin3).
            // subset_placeholder.from_join(&subset_placeholder_o2, &subset, |&_origin2, &origin1, &origin3| (origin1, origin3));

            // borrow_live_at(loan, point) :-
            //   requires(origin, loan),
            //   region_live_at(origin, point)
            //
            // potential_errors(loan, point) :-
            //   invalidates(loan, point),
            //   borrow_live_at(loan, point).
            //
            // Note: we don't need to materialize `borrow_live_at` here
            // so we can inline it in the `potential_errors` relation.
            //
            potential_errors.from_leapjoin(
                &requires,
                (
                    region_live_at.extend_with(|&(origin, _loan)| origin),
                    invalidates.extend_with(|&(_origin, loan)| loan),
                ),
                |&(_origin, loan), &point| (loan, point),
            );

            // potential_subset_errors(Origin1, Origin2) :-
            //   subset_placeholder(Origin1, Origin2),
            //   placeholder_origin(Origin2),
            //   !known_subset(Origin1, Origin2).
            // potential_subset_errors.from_leapjoin(
            //     &subset_placeholder,
            //     (
            //         placeholder_origin.extend_with(|&(_origin1, origin2)| origin2),
            //         known_subset.filter_anti(|&(origin1, origin2)| (origin1, origin2)),
            //         // remove symmetries:
            //         datafrog::ValueFilter::from(|&(origin1, origin2), ()| {
            //             origin2 != origin1
            //         }),
            //     ),
            //     |&(origin1, origin2), _| (origin1, origin2),
            // );

            // potential_subset_errors(Origin1, Origin2) :-
            //   requires(Origin2, Loan1),
            //   placeholder(Origin2, _),
            //   placeholder(Origin1, Loan1),
            //   !known_contains(Origin2, Loan1).
            potential_subset_errors.from_leapjoin(
                &requires,
                (
                    placeholder_origin.filter_with(|&(origin2, _loan1)| (origin2, ())),
                    placeholder_loan.extend_with(|&(_origin2, loan1)| loan1),
                    known_contains.filter_anti(|&(origin2, loan1)| (origin2, loan1)),
                    // remove symmetries:
                    datafrog::ValueFilter::from(|&(origin2, _loan1), &origin1| origin2 != origin1),
                ),
                |&(origin2, _loan1), &origin1| (origin1, origin2),
            );
        }

        // let subset_placeholder = subset_placeholder.complete();
        // println!("subset_placeholder: {}", subset_placeholder.len());
        // // println!("subset_placeholder: {:#?}", subset_placeholder.elements);

        let potential_subset_errors = potential_subset_errors.complete();
        println!("potential_subset_errors: {}", potential_subset_errors.len());
        // println!("potential_subset_errors: {:#?}", potential_subset_errors.elements);

        for &(origin1, origin2) in potential_subset_errors.iter() {
            result
                .subset_errors
                .entry(0.into())
                .or_default()
                .insert((origin1, origin2));
        }

        if result.dump_enabled {
            let subset = subset.complete();
            for &(origin1, origin2) in subset.iter() {
                result
                    .subset_anywhere
                    .entry(origin1)
                    .or_default()
                    .insert(origin2);
            }

            let requires = requires.complete();
            for &(origin, loan) in requires.iter() {
                result
                    .restricts_anywhere
                    .entry(origin)
                    .or_default()
                    .insert(loan);
            }
        }

        potential_errors.complete()
    };

    info!(
        "potential_errors is complete: {} tuples, {:?}",
        potential_errors.len(),
        timer.elapsed()
    );

    potential_errors
}
