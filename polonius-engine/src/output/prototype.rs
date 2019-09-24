//! A version of the Prototype analysis.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::time::Instant;

use crate::output::initialization;
use crate::output::liveness;
use crate::output::Output;
use facts::{AllFacts, Atom};

use datafrog::{Iteration, Relation, RelationLeaper};

pub(super) fn compute<Origin: Atom, Loan: Atom, Point: Atom, Variable: Atom, MovePath: Atom>(
    dump_enabled: bool,
    all_facts: AllFacts<Origin, Loan, Point, Variable, MovePath>,
) -> Output<Origin, Loan, Point, Variable, MovePath> {
    
    let use_flow_sensitive_equality = {
        if let Ok(flag) = std::env::var("POLONIUS_FLOW_SENSITIVE") {
            match flag.as_ref() {
                "0" => false,
                "1" => true,
                _ => flag.parse::<bool>().unwrap_or(false)
            }            
        } else {
            false
        }
    };

    if use_flow_sensitive_equality {
        compute_flow_sensitive_equality(dump_enabled, all_facts)
    } else {
        compute_static_equality(dump_enabled, all_facts)
    }
}

// Prototype variant: works probably like `compute_static_equality`, ie probably 2 failures in rustc
fn compute_flow_sensitive_equality<Origin: Atom, Loan: Atom, Point: Atom, Variable: Atom, MovePath: Atom>(
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

    let computation_start = Instant::now();

    // The invalidated loans are the only loans which could cause errors
    let invalidates_set = all_facts.invalidates.iter().map(|&(_p, l)| l).collect::<HashSet<_>>();

    // The "interesting" borrow regions are the ones referring to loans for which an error could occur
    let start = Instant::now();
    let interesting_borrow_region: Relation<_> = all_facts
                .borrow_region
                .iter()
                .filter(|&(_r, l, _p)| invalidates_set.contains(l))
                .collect();
    println!("interesting_borrow_region relation computed: {} tuples vs {}, in {} ms", interesting_borrow_region.len(), all_facts.borrow_region.len(), start.elapsed().as_millis());

    // The interesting regions are any region into which an interesting loan could flow
    let start = Instant::now();
    let interesting_region = {
        let mut iteration = Iteration::new();

        let outlives_r1 =
            Relation::from_iter(all_facts.outlives.iter().map(|&(r1, r2, _p)| (r1, r2)));
        let interesting_region = iteration.variable::<(Origin, ())>("interesting_region");

        // interesting_region(R) :- interesting_borrow_region(R, _, _);
        interesting_region
            .extend(interesting_borrow_region.iter().map(|&(r, _l, _p)| (r, ())));

        while iteration.changed() {
            // interesting_region(R2) :-
            //     outlives(R1, R2, _),
            //     interesting_region(R1, _, _);
            interesting_region.from_join(
                &interesting_region,
                &outlives_r1,
                |_r1, (), &r2| (r2, ()),
            );
        }

        interesting_region.complete().iter().map(|&(r1, _)| r1).collect::<HashSet<_>>()
    };

    println!("interesting_region relation computed: {} tuples, in {} ms", interesting_region.len(), start.elapsed().as_millis());

    // Limit the `subset` relation to interesting regions
    
    let interesting_outlives = all_facts
            .outlives
            .iter()
            .filter(|&(r1, _r2, _p)| interesting_region.contains(r1));
    println!("interesting_outlives relation computed: {} tuples vs {}", interesting_outlives.clone().count(), all_facts.outlives.len());

    // 1 - compute subsets TC
    // Subset filtering optimization: there's no need to do the TC
    // including origins which are not interesting. Only the interesting loans flowing
    // into origins (interesting origins) can be the source of errors if they're live
    // when the loan is invalidated. Any origin not containing an interesting loan
    // will be filtered out by the end of the computation anyway.
    let start = Instant::now();
    let subsets = {
        let mut iteration = Iteration::new();

        let subset = iteration.variable::<(Origin, Origin, Point)>("subset");

        let subset_base = Relation::from_iter(
            interesting_outlives
                .clone()
                .map(|&(r1, r2, p)| ((r1, p), r2))
        );

        let subset_r1p = iteration.variable_indistinct("subset_r1p");

        // subset(R1, R2, P) :- outlives(R1, R2, P).
        subset.extend(interesting_outlives);

        while iteration.changed() {
            subset_r1p.from_map(&subset, |&(r1, r2, p)| ((r1, p), r2));

            // a leaper that rejects symmetries from proposed values to the
            // leapjoin: origins which are `subsets` of themselves
            let reject_symmetries = datafrog::ValueFilter::from(|&((r1, _p), _r2), &r3| r1 != r3);

            // subset(R1, R3, P) :-
            //   subset(R1, R2, P),
            //   subset_base(R2, R3, P).
            // subset.from_join(&subset_r2p, &subset_r1p, |&(_r2, p), &r1, &r3| (r1, r3, p));            
            subset.from_leapjoin(
                &subset_r1p,
                (
                    subset_base.extend_with(|&((_r1, p), r2)| (r2, p)),
                    reject_symmetries,
                ),
                |&((r1, p), _r2), &r3| (r1, r3, p),
            );
        }

        subset.complete()
    };
    debug_assert_eq!(subsets.iter().filter(|&(r1, r2, _)| r1 == r2).count(), 0);

    println!("subsets relation computed: {} tuples in {} ms", subsets.len(), start.elapsed().as_millis());
    // println!("subsets: {:#?}", subsets.elements);

    // 2 - compute region equality
    // (could be done in datalog, not the case here just 
    // for flexibility and verification purposes while developping the variant)
    // let start = Instant::now();
    let equals = {
        let sets: HashSet<_> = subsets.iter().collect();
        Relation::from_iter(
            subsets
                .iter()
                .filter(|(r1, r2, p)| sets.contains(&(*r2, *r1, *p)))
                .map(|&(r1, r2, p)| ((r1, p), r2))
        )
    };
    debug_assert_eq!(equals.iter().filter(|&((r1, _p), r2)| r1 == r2).count(), 0);

    println!("equals relation computed: {} tuples in {} ms", equals.len(), start.elapsed().as_millis());
    // println!("equals: {:?}", equals.elements);

    // 3 - compute provenance information and check illegal accesses
    let errors = {
        // Create a new iteration context, ...
        let mut iteration = Iteration::new();

        // static inputs
        let subsets_r1p = Relation::from_iter(subsets.iter().map(|&(r1, r2, p)| ((r1, p), r2)));

        let equal_r1p = iteration.variable::<((Origin, Point), Origin)>("equal");
        equal_r1p.insert(equals);

        let cfg_edge_rel: Relation<(Point, Point)> = all_facts.cfg_edge.into();

        // note: since we're only interested in the _absence_ of a particular tuple
        // (`killed` is always used in an antijoin), we could use a probabilistic data
        // structure with no false-negatives like a Bloom filter. This relation is
        // usually small, `clap` used to have around 1000, so the memory savings might not be incredible
        // in the absolute, the relation size would be a lot smaller, for a one-time insertion slowdown (2x or so 
        // compared to a HashSet) and relatively similary query time. 
        let killed_rel: Relation<(Loan, Point)> = all_facts.killed.into(); 

        // .. some variables, ..
        let requires = iteration.variable::<(Origin, Loan, Point)>("requires");
        let borrow_live_at = iteration.variable::<((Loan, Point), ())>("borrow_live_at");

        // `invalidates` facts, stored ready for joins
        let invalidates = iteration.variable_indistinct::<((Loan, Point), ())>("invalidates");
        invalidates.extend(all_facts.invalidates.iter().map(|&(p, b)| ((b, p), ())));

        // different index for `requires`.
        let requires_rp = iteration.variable_indistinct("requires_rp");

        // we need `region_live_at` in both variable and relation forms.
        // (respectively, for the regular join and the leapjoin).
        // note: we're only interested in the presence of tuples in `region_live_at`,
        // we never produce tuples only filter. We could use a different datastructure.
        let region_live_at_var = iteration.variable_indistinct::<((Origin, Point), ())>("region_live_at");
        let region_live_at_rel = Relation::from_iter(region_live_at.iter().cloned());

        region_live_at_var.extend(region_live_at.iter().map(|&(r, p)| ((r, p), ())));

        // output
        let errors = iteration.variable("errors");

        // requires(R, L, P) :- borrow_region(R, L, P).
        // requires.insert(all_facts.borrow_region.into());

        // efficiency: limit computing this relation to "interesting loans". The others _cannot_ produce errors, 
        // so they would be filtered out by the end of the computation anyway. We'll filter them out early
        // and not track them along the CFG.
        requires.insert(interesting_borrow_region);

        while iteration.changed() {
            requires_rp.from_map(&requires, |&(r, b, p)| ((r, p), b));

            // requires(R2, L, P) :-
            //   requires(R1, L, P),
            //   subset(R1, R2, P).
            requires.from_join(&requires_rp, &subsets_r1p, |&(_r1, p), &l, &r2| (r2, l, p));
            
            // the following is the same join, but if Leapers of size 1 were added back to datafrog
            // requires.from_leapjoin(
            //     &requires,
            //     (
            //         subsets_r1p.extend_with(|&(r, _l, p)| (r, p)),
            //     ),
            //     |&(_r1, l, p), &r2| (r2, l, p),
            // );

            // flow sensitive equality derived from https://github.com/rust-lang/polonius/issues/107#issuecomment-499427026 ...
            //
            // requires(R2, L, P) :-
            //   requires(R1, L, P),
            //   equal(R1, R2, P).
            requires.from_join(&requires_rp, &equal_r1p, |&(_r1, p), &l, &r2| (r2, l, p));

            // equal(R1, R2, Q) :-
            //   equal(R1, R2, P),
            //   cfg_edge(P, Q).
            equal_r1p.from_leapjoin(
                &equal_r1p,
                (
                    cfg_edge_rel.extend_with(|&((_r1, p), _r2)| p),
                    datafrog::PrefixFilter::from(|_| true)
                    // ^^^ HACK: either have Leapers of size 1
                    // or introduce a `equal_p` index to use a regular join
                    // best to compare both to see how they each perform
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

            // errors(B, P) :-
            //   invalidates(B, P),
            //   borrow_live_at(B, P).
            errors.from_join(&invalidates, &borrow_live_at, |&(b, p), &(), &()| (b, p));

            // note: the 2 previous joins could be expressed as a single leapjoin when we relax
            // the WF-ness in datafrog, like this (which compiles but will fail at runtime, because
            // there is no `extend_` call):
            //
            // errors(B, P) :-
            //   requires(R, B, P),
            //   invalidates(B, P),
            //   region_live_at(R, P).
            //
            // errors.from_leapjoin(
            //     &requires,
            //     (
            //         invalidates_rel.filter_with(|&(r, b, p)| (b, p)),
            //         region_live_at_rel.filter_with(|&(r, b, p)| (r, b)),
            //     ),
            //     |&(r, b, p), ()| (b, p)
            // );
        }

        if dump_enabled {
            assert!(
                subsets_r1p.iter().filter(|&((r1, _p), r2)| r1 == r2).count() == 0,
                "unwanted subset symmetries"
            );
            for ((r1, location), r2) in subsets_r1p.iter() {
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

// Prototype variant: doesn't work, 2 errors in rustc, both compiling code which shouldn't compile
fn compute_static_equality<Origin: Atom, Loan: Atom, Point: Atom, Variable: Atom, MovePath: Atom>(
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

    let computation_start = Instant::now();

    let invalidates_set = all_facts.invalidates.iter().map(|&(_p, l)| l).collect::<HashSet<_>>();

    let interesting_borrow_region: Relation<_> = all_facts
                .borrow_region
                .iter()
                .filter(|&(_r, l, _p)| invalidates_set.contains(l))
                .collect();
    // println!("interesting_borrow_region relation computed: {} tuples vs {}", interesting_borrow_region.len(), all_facts.borrow_region.len());

    let interesting_region = {
        let mut iteration = Iteration::new();

        let outlives_r1 =
            Relation::from_iter(all_facts.outlives.iter().map(|&(r1, r2, _p)| (r1, r2)));
        let interesting_region = iteration.variable::<(Origin, ())>("interesting_region");

        // interesting_region(R) :- interesting_borrow_region(R, _, _);
        interesting_region
            .extend(interesting_borrow_region.iter().map(|&(r, _l, _p)| (r, ())));

        while iteration.changed() {
            // interesting_region(R2) :-
            //     outlives(R1, R2, _),
            //     interesting_region(R1, _, _);
            interesting_region.from_join(
                &interesting_region,
                &outlives_r1,
                |_r1, (), &r2| (r2, ()),
            );
        }

        interesting_region.complete().iter().map(|&(r1, _)| r1).collect::<HashSet<_>>()
    };
    // println!("interesting_region relation computed: {} tuples", interesting_region.len());

    let interesting_outlives = all_facts
            .outlives
            .iter()
            .filter(|&(r1, _r2, _p)| interesting_region.contains(r1));
    // println!("interesting_outlives relation computed: {} tuples vs {}", interesting_outlives.clone().count(), all_facts.outlives.len());

    // 1 - compute subsets TC
    let subsets = {
        let mut iteration = Iteration::new();

        let subset = iteration.variable::<(Origin, Origin, Point)>("subset");

        let subset_base = Relation::from_iter(
            interesting_outlives
                .clone()
                .map(|&(r1, r2, p)| ((r1, p), r2))
        );

        let subset_r1p = iteration.variable_indistinct("subset_r1p");

        // subset(R1, R2, P) :- outlives(R1, R2, P). 
        subset.extend(interesting_outlives);

        while iteration.changed() {
            subset_r1p.from_map(&subset, |&(r1, r2, p)| ((r1, p), r2));

            // a leaper that removes symmetries from proposed values to the
            // leapjoin: origins which are `subsets` of themselves
            let remove_symmetries = datafrog::ValueFilter::from(|&((r1, _p), _r2), &r3| r1 != r3);

            // subset(R1, R3, P) :-
            //   subset(R1, R2, P),
            //   subset_base(R2, R3, P).
            // subset.from_join(&subset_r2p, &subset_r1p, |&(_r2, p), &r1, &r3| (r1, r3, p));            
            subset.from_leapjoin(
                &subset_r1p,
                (
                    subset_base.extend_with(|&((_r1, p), r2)| (r2, p)),
                    remove_symmetries,
                ),
                |&((r1, p), _r2), &r3| (r1, r3, p),
            );
        }

        subset.complete()
    };
    debug_assert_eq!(subsets.iter().filter(|&(r1, r2, _)| r1 == r2).count(), 0);
    // println!("subset relation computed: {} tuples", subsets.elements.len());

    // 2 - compute region equality
    let equals = {
        let sets: HashSet<_> = subsets.iter().collect();
        Relation::from_iter(
            subsets
                .iter()
                .filter(|(r1, r2, p)| sets.contains(&(*r2, *r1, *p)))
                .map(|&(r1, r2, _)| (r1, r2)),
        )
    };
    // println!("equals relation computed: {} tuples", equals.elements.len());
    // println!("equals: {:?}", equals.elements);

    // 3 - compute provenance information and check illegal accesses
    let errors = {
        // Create a new iteration context, ...
        let mut iteration = Iteration::new();

        // static inputs
        let subset = iteration.variable_indistinct::<(Origin, Origin, Point)>("subset");
        subset.insert(subsets);

        let equal = iteration.variable_indistinct::<(Origin, Origin)>("equal");
        equal.insert(equals);

        let cfg_edge_rel: Relation<(Point, Point)> = all_facts.cfg_edge.into();
        let killed_rel: Relation<(Loan, Point)> = all_facts.killed.into();
        
        // .. some variables, ..        
        let requires = iteration.variable::<(Origin, Loan, Point)>("requires");
        let borrow_live_at = iteration.variable::<((Loan, Point), ())>("borrow_live_at");

        // `invalidates` facts, stored ready for joins
        let invalidates = iteration.variable_indistinct::<((Loan, Point), ())>("invalidates");
        invalidates.extend(all_facts.invalidates.iter().map(|&(p, b)| ((b, p), ())));

        // different indices for `subset`.
        let subset_r1p = iteration.variable_indistinct("subset_r1p");

        // different index for `requires`.
        let requires_rp = iteration.variable_indistinct("requires_rp");
        let requires_r = iteration.variable_indistinct("requires_r");

        // we need `region_live_at` in both variable and relation forms.
        // (respectively, for the regular join and the leapjoin).
        let region_live_at_var = iteration.variable_indistinct::<((Origin, Point), ())>("region_live_at");
        let region_live_at_rel = Relation::from_iter(region_live_at.iter().cloned());

        region_live_at_var.extend(region_live_at.iter().map(|&(r, p)| ((r, p), ())));

        // output
        let errors = iteration.variable("errors");

        // requires(R, L, P) :- borrow_region(R, L, P).
        // requires.insert(all_facts.borrow_region.into());

        // efficiency: limit computing this relation to "interesting loans". The others _cannot_ produce errors, 
        // so they would be filtered out by the end of the computation anyway. We'll filter them out early
        // and not track them along the CFG.
        requires.insert(interesting_borrow_region);

        while iteration.changed() {
            subset
                .recent
                .borrow_mut()
                .elements
                .retain(|&(r1, r2, _)| r1 != r2);

            // remap fields to re-index by keys.
            subset_r1p.from_map(&subset, |&(r1, r2, p)| ((r1, p), r2));
            requires_rp.from_map(&requires, |&(r, b, p)| ((r, p), b));
            requires_r.from_map(&requires, |&(r, b, p)| (r, (b, p)));

            // requires(R2, L, P) :-
            //   requires(R1, L, P),
            //   subset(R1, R2, P).
            requires.from_join(&requires_rp, &subset_r1p, |&(_r1, p), &l, &r2| (r2, l, p));

            // requires(R1, L, P) :-
            //   requires(R2, L, P),
            //   equals(R1, R2).
            requires.from_join(&requires_r, &equal, |&_r2, &(l, p), &r1| (r1, l, p));

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

            // errors(B, P) :- 
            //   invalidates(B, P), 
            //   borrow_live_at(B, P).
            errors.from_join(&invalidates, &borrow_live_at, |&(b, p), &(), &()| (b, p));

            // note: the 2 previous joins could be expressed as a single leapjoin when we relax
            // the WF-ness in datafrog, like this (which compiles but will fail at runtime, because
            // there is no `extend_` call):
            //
            // errors.from_leapjoin(
            //     &requires,
            //     (
            //         invalidates_rel.filter_with(|&(r, b, p)| (b, p)),
            //         region_live_at_rel.filter_with(|&(r, b, p)| (r, b)),
            //     ),
            //     |&(r, b, p), ()| (b, p)
            // );
        }

        if dump_enabled {
            let subset = subset.complete();
            assert!(
                subset.iter().filter(|&(r1, r2, _)| r1 == r2).count() == 0,
                "unwanted subset symmetries"
            );
            for (r1, r2, location) in &subset.elements {
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