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

    // Static inputs
    let region_live_at = &ctx.region_live_at;
    let invalidates = &ctx.invalidates;
    let placeholder_origin = &ctx.placeholder_origin;
    let placeholder_loan = &ctx.placeholder_loan;
    let known_contains = &ctx.known_contains;

    // subset(origin1, origin2) :- outlives(origin1, origin2, _point)
    let subset = Relation::from_iter(
        ctx.outlives
            .iter()
            .map(|&(origin1, origin2, _point)| (origin1, origin2)),
    );

    // Create a new iteration context, ...
    let mut iteration = Iteration::new();

    // .. some variables, ..
    let requires = iteration.variable::<(T::Origin, T::Loan)>("requires");

    let potential_errors = iteration.variable::<(T::Loan, T::Point)>("potential_errors");
    let potential_subset_errors =
        iteration.variable::<(T::Origin, T::Origin)>("potential_subset_errors");

    // load initial facts.

    // requires(origin, loan) :-
    //   borrow_region(origin, loan, _point).
    requires.extend(
        ctx.borrow_region
            .iter()
            .map(|&(origin, loan, _point)| (origin, loan)),
    );

    // requires(origin, loan) :-
    //  placeholder_loan(origin, loan).
    requires.extend(
        placeholder_loan
            .iter()
            .map(|&(loan, origin)| (origin, loan)),
    );

    // .. and then start iterating rules!
    while iteration.changed() {
        // requires(origin2, loan) :-
        //   requires(origin1, loan),
        //   subset(origin1, origin2).
        requires.from_join(&requires, &subset, |&_origin1, &loan, &origin2| {
            (origin2, loan)
        });

        // potential_errors(loan, point) :-
        //   invalidates(loan, point),
        //   borrow_live_at(loan, point).
        //
        // borrow_live_at(loan, point) :-
        //   requires(origin, loan),
        //   region_live_at(origin, point)
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

    if result.dump_enabled {
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

    let potential_errors = potential_errors.complete();
    let potential_subset_errors = potential_subset_errors.complete();

    // TMP: the error location is meaningless for a location-insensitive subset error analysis
    for &(origin1, origin2) in potential_subset_errors.iter() {
        result
            .subset_errors
            .entry(0.into())
            .or_default()
            .insert((origin1, origin2));
    }

    info!(
        "location_insensitive is complete: {} `potential_errors` tuples, {} `potential_subset_errors` tuples, {:?}",
        potential_errors.len(),
        potential_subset_errors.len(),
        timer.elapsed()
    );

    potential_errors
}
