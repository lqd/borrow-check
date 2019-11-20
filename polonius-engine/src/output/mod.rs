// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use datafrog::Relation;
use rustc_hash::{FxHashMap, FxHashSet};
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use crate::facts::{AllFacts, Atom, FactTypes};

mod datafrog_opt;
mod initialization;
mod liveness;
mod location_insensitive;
mod naive;

#[derive(Debug, Clone, Copy)]
pub enum Algorithm {
    /// Simple rules, but slower to execute
    Naive,

    /// Optimized variant of the rules
    DatafrogOpt,

    /// Fast to compute, but imprecise: there can be false-positives
    /// but no false-negatives. Tailored for quick "early return" situations.
    LocationInsensitive,

    /// Compares the `Naive` and `DatafrogOpt` variants to ensure they indeed
    /// compute the same errors.
    Compare,

    /// Combination of the fast `LocationInsensitive` pre-pass, followed by
    /// the more expensive `DatafrogOpt` variant.
    Hybrid,
}

impl Algorithm {
    /// Optimized variants that ought to be equivalent to "naive"
    pub const OPTIMIZED: &'static [Algorithm] = &[Algorithm::DatafrogOpt];

    pub fn variants() -> [&'static str; 5] {
        [
            "Naive",
            "DatafrogOpt",
            "LocationInsensitive",
            "Compare",
            "Hybrid",
        ]
    }
}

impl ::std::str::FromStr for Algorithm {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_ref() {
            "naive" => Ok(Algorithm::Naive),
            "datafrogopt" => Ok(Algorithm::DatafrogOpt),
            "locationinsensitive" => Ok(Algorithm::LocationInsensitive),
            "compare" => Ok(Algorithm::Compare),
            "hybrid" => Ok(Algorithm::Hybrid),
            _ => Err(String::from(
                "valid values: Naive, DatafrogOpt, LocationInsensitive, Compare, Hybrid",
            )),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Output<T: FactTypes> {
    pub errors: FxHashMap<T::Point, Vec<T::Loan>>,
    pub subset_errors: FxHashMap<T::Point, BTreeSet<(T::Origin, T::Origin)>>,

    pub dump_enabled: bool,

    // these are just for debugging
    pub borrow_live_at: FxHashMap<T::Point, Vec<T::Loan>>,
    pub restricts: FxHashMap<T::Point, BTreeMap<T::Origin, BTreeSet<T::Loan>>>,
    pub restricts_anywhere: FxHashMap<T::Origin, BTreeSet<T::Loan>>,
    pub region_live_at: FxHashMap<T::Point, Vec<T::Origin>>,
    pub invalidates: FxHashMap<T::Point, Vec<T::Loan>>,
    pub subset: FxHashMap<T::Point, BTreeMap<T::Origin, BTreeSet<T::Origin>>>,
    pub subset_anywhere: FxHashMap<T::Origin, BTreeSet<T::Origin>>,
    pub var_live_at: FxHashMap<T::Point, Vec<T::Variable>>,
    pub var_drop_live_at: FxHashMap<T::Point, Vec<T::Variable>>,
    pub path_maybe_initialized_at: FxHashMap<T::Point, Vec<T::Path>>,
    pub var_maybe_initialized_on_exit: FxHashMap<T::Point, Vec<T::Variable>>,
    pub known_contains: FxHashMap<T::Origin, BTreeSet<T::Loan>>,
}

/// Subset of `AllFacts` dedicated to initialization
struct InitializationContext<T: FactTypes> {
    child: Vec<(T::Path, T::Path)>,
    path_belongs_to_var: Vec<(T::Path, T::Variable)>,
    initialized_at: Vec<(T::Path, T::Point)>,
    moved_out_at: Vec<(T::Path, T::Point)>,
    path_accessed_at: Vec<(T::Path, T::Point)>,
}

/// Subset of `AllFacts` dedicated to liveness
struct LivenessContext<T: FactTypes> {
    var_used: Vec<(T::Variable, T::Point)>,
    var_defined: Vec<(T::Variable, T::Point)>,
    var_drop_used: Vec<(T::Variable, T::Point)>,
    var_uses_region: Vec<(T::Variable, T::Origin)>,
    var_drops_region: Vec<(T::Variable, T::Origin)>,
}

/// Subset of `AllFacts` dedicated to borrow checking, and data ready to use by the variants
struct Context<'ctx, T: FactTypes> {
    // `Relation`s used as static inputs, by all variants
    region_live_at: Relation<(T::Origin, T::Point)>,
    invalidates: Relation<(T::Loan, T::Point)>,

    // static inputs used via `Variable`s, by all variants
    outlives: &'ctx Vec<(T::Origin, T::Origin, T::Point)>,
    borrow_region: &'ctx Vec<(T::Origin, T::Loan, T::Point)>,

    // static inputs used by variants other than `LocationInsensitive`
    cfg_node: &'ctx BTreeSet<T::Point>,
    killed: Relation<(T::Loan, T::Point)>,
    known_contains: Relation<(T::Origin, T::Loan)>,
    placeholder_origin: Relation<(T::Origin, ())>,
    placeholder_loan: Relation<(T::Loan, T::Origin)>,

    // while this static input is unused by `LocationInsensitive`, it's depended on by initialization
    // and liveness, so already computed by the time we get to borrowcking.
    cfg_edge: Relation<(T::Point, T::Point)>,

    // Partial results possibly used by other variants as input
    potential_errors: Option<FxHashSet<T::Loan>>,

    // interesting-ness filtering
    interesting_origin: FxHashSet<T::Origin>,
    interesting_borrow_region: Relation<(T::Origin, T::Loan, T::Point)>,
}

impl<T: FactTypes> Output<T> {
    /// All variants require the same initial preparations, done in multiple
    /// successive steps:
    /// - compute initialization data
    /// - compute liveness
    /// - prepare static inputs as shared `Relation`s
    /// - in cases where `LocationInsensitive` variant is ran as a filtering pre-pass,
    ///   partial results can also be stored in the context, so that the following
    ///   variant can use it to prune its own input data
    pub fn compute(all_facts: &AllFacts<T>, algorithm: Algorithm, dump_enabled: bool) -> Self {
        let mut result = Output::new(dump_enabled);

        // TODO: remove all the cloning thereafter, but that needs to be done in concert with rustc

        let cfg_edge = all_facts.cfg_edge.clone().into();

        // The set of "interesting" loans
        let interesting_loan: FxHashSet<_> = all_facts
            .invalidates
            .iter()
            .map(|&(_point, loan)| loan)
            .collect();

        // The "interesting" borrow regions are the ones referring to loans for which an error could occur
        let interesting_borrow_region: Relation<_> = all_facts
            .borrow_region
            .iter()
            .filter(|&(_origin, loan, _point)| interesting_loan.contains(loan))
            .collect();

        // The interesting origins are:
        // - for illegal access errors: any origin into which an interesting loan could flow.
        // - for illegal subset relation errors: any placeholder origin. (TODO: this can likely
        //   be tightened further to some of the placeholders which are _not_ in the
        //   `known_subset` relation: they are the only ones into which an unexpected placeholder
        //   loan can flow)
        let interesting_origin = {
            use datafrog::Iteration;

            let mut iteration = Iteration::new();

            let outlives_o1 = Relation::from_iter(
                all_facts
                    .outlives
                    .iter()
                    .map(|&(origin1, origin2, _point)| (origin1, origin2)),
            );

            let interesting_origin = iteration.variable::<(T::Origin, ())>("interesting_origin");

            // interesting_origin(Origin) :-
            //   interesting_borrow_region(Origin, _, _);
            interesting_origin.extend(
                interesting_borrow_region
                    .iter()
                    .map(|&(origin, _loan, _point)| (origin, ())),
            );

            // interesting_origin(Origin) :-
            //   placeholder(Origin, _);
            interesting_origin.extend(
                all_facts
                    .placeholder
                    .iter()
                    .map(|&(origin, _loan)| (origin, ())),
            );

            while iteration.changed() {
                // interesting_origin(Origin2) :-
                //   outlives(Origin1, Origin2, _),
                //   interesting_origin(Origin1, _, _);
                interesting_origin.from_join(
                    &interesting_origin,
                    &outlives_o1,
                    |_origin1, (), &origin2| (origin2, ()),
                );
            }

            interesting_origin
                .complete()
                .iter()
                .map(|&(origin1, _)| origin1)
                .collect::<FxHashSet<_>>()
        };

        // 1) Initialization
        let initialization_ctx = InitializationContext {
            child: all_facts.child.clone(),
            path_belongs_to_var: all_facts.path_belongs_to_var.clone(),
            initialized_at: all_facts.initialized_at.clone(),
            moved_out_at: all_facts.moved_out_at.clone(),
            path_accessed_at: all_facts.path_accessed_at.clone(),
        };

        let var_maybe_initialized_on_exit = initialization::init_var_maybe_initialized_on_exit(
            initialization_ctx,
            &cfg_edge,
            &mut result,
        );

        // 2) Liveness
        let liveness_ctx = LivenessContext {
            var_used: all_facts.var_used.clone(),
            var_defined: all_facts.var_defined.clone(),
            var_drop_used: all_facts.var_drop_used.clone(),
            var_uses_region: all_facts.var_uses_region.clone(),
            var_drops_region: all_facts.var_drops_region.clone(),
        };

        let mut region_live_at = liveness::compute_live_regions(
            liveness_ctx,
            &cfg_edge,
            var_maybe_initialized_on_exit,
            &mut result,
        );

        let cfg_node = cfg_edge
            .iter()
            .map(|&(point1, _)| point1)
            .chain(cfg_edge.iter().map(|&(_, point2)| point2))
            .collect();

        liveness::make_universal_regions_live::<T>(
            &mut region_live_at,
            &cfg_node,
            &all_facts.universal_region,
        );

        // 3) Borrow checking

        // Prepare data as datafrog relations, ready to join.
        //
        // Note: if rustc and polonius had more interaction, we could also delay or avoid
        // generating some of the facts that are now always present here. For example,
        // the `LocationInsensitive` variant doesn't use the `killed` or `invalidates`
        // relations, so we could technically delay passing them from rustc, when
        // using this or the `Hybrid` variant, to after the pre-pass has made sure
        // we actually need to compute the full analysis. If these facts happened to
        // be recorded in separate MIR walks, we might also avoid generating those facts.

        let region_live_at = region_live_at.into();

        // TODO: also flip the order of this relation's arguments in rustc
        // from `invalidates(point, loan)` to `invalidates(loan, point)`.
        // to avoid this allocation.
        let invalidates = Relation::from_iter(
            all_facts
                .invalidates
                .iter()
                .map(|&(point, loan)| (loan, point)),
        );

        let killed = all_facts.killed.clone().into();

        // `known_subset` is a list of all the `'a: 'b` subset relations the user gave:
        // it's not required to be transitive. `known_contains` is its transitive closure: a list
        // of all the known placeholder loans that each of these placeholder origins contains.
        // Given the `known_subset`s `'a: 'b` and `'b: 'c`: in the `known_contains` relation, `'a`
        // will also contain `'c`'s placeholder loan.
        let known_subset = all_facts.known_subset.clone().into();
        let known_contains =
            Output::<T>::compute_known_contains(&known_subset, &all_facts.placeholder);

        let placeholder_origin: Relation<_> = Relation::from_iter(
            all_facts
                .universal_region
                .iter()
                .map(|&origin| (origin, ())),
        );

        // TODO: flip the relation's arguments order in the input facts ?
        let placeholder_loan = Relation::from_iter(
            all_facts
                .placeholder
                .iter()
                .map(|&(origin, loan)| (loan, origin)),
        );

        // Ask the variants to compute errors in their own way
        let mut ctx = Context {
            region_live_at,
            invalidates,
            cfg_edge,
            cfg_node: &cfg_node,
            outlives: &all_facts.outlives,
            borrow_region: &all_facts.borrow_region,
            killed,
            known_contains,
            placeholder_origin,
            placeholder_loan,
            potential_errors: None,

            interesting_origin,
            interesting_borrow_region,
        };

        let errors = match algorithm {
            Algorithm::LocationInsensitive => location_insensitive::compute(&ctx, &mut result),
            Algorithm::Naive => {
                let (errors, subset_errors) = naive::compute(&ctx, &mut result);

                // Record illegal subset errors
                for &(origin1, origin2, location) in subset_errors.iter() {
                    result
                        .subset_errors
                        .entry(location)
                        .or_default()
                        .insert((origin1, origin2));
                }

                errors
            }
            Algorithm::DatafrogOpt => datafrog_opt::compute(&ctx, &mut result),
            Algorithm::Hybrid => {
                // WIP: the `LocationInsensitive` variant doesn't compute any illegal subset
                // relation errors. So using it as a quick pre-filter for illegal accesses
                // errors will also end up skipping checking for subset errors.

                // Execute the fast `LocationInsensitive` computation as a pre-pass:
                // if it finds no possible errors, we don't need to do the more complex
                // computations as they won't find errors either, and we can return early.
                let potential_errors = location_insensitive::compute(&ctx, &mut result);
                if potential_errors.is_empty() {
                    potential_errors
                } else {
                    // Record these potential errors as they can be used to limit the next
                    // variant's work to only these loans.
                    ctx.potential_errors =
                        Some(potential_errors.iter().map(|&(loan, _)| loan).collect());

                    datafrog_opt::compute(&ctx, &mut result)
                }
            }
            Algorithm::Compare => {
                // Ensure the `Naive` and `DatafrogOpt` errors are the same
                let (naive_errors, _) = naive::compute(&ctx, &mut result);
                let opt_errors = datafrog_opt::compute(&ctx, &mut result);

                // TODO: compare illegal subset relations errors as well here ?

                let mut naive_errors_by_point = FxHashMap::default();
                for &(loan, point) in naive_errors.iter() {
                    naive_errors_by_point
                        .entry(point)
                        .or_insert(Vec::new())
                        .push(loan);
                }

                let mut opt_errors_by_point = FxHashMap::default();
                for &(loan, point) in opt_errors.iter() {
                    opt_errors_by_point
                        .entry(point)
                        .or_insert(Vec::new())
                        .push(loan);
                }

                if compare_errors(&naive_errors_by_point, &opt_errors_by_point) {
                    panic!(concat!(
                        "The errors reported by the naive algorithm differ from ",
                        "the errors reported by the optimized algorithm. ",
                        "See the error log for details."
                    ));
                } else {
                    debug!("Naive and optimized algorithms reported the same errors.");
                }

                naive_errors
            }
        };

        // Record illegal access errors
        for &(loan, location) in errors.iter() {
            result.errors.entry(location).or_default().push(loan);
        }

        // Record more debugging info when asked to do so
        if dump_enabled {
            for &(origin, location) in ctx.region_live_at.iter() {
                result
                    .region_live_at
                    .entry(location)
                    .or_default()
                    .push(origin);
            }

            for &(origin, loan) in ctx.known_contains.iter() {
                result
                    .known_contains
                    .entry(origin)
                    .or_default()
                    .insert(loan);
            }
        }

        result
    }

    /// Computes the transitive closure of the `known_subset` relation, so that we have
    /// the full list of placeholder loans contained by the placeholder origins.
    fn compute_known_contains(
        known_subset: &Relation<(T::Origin, T::Origin)>,
        placeholder: &Vec<(T::Origin, T::Loan)>,
    ) -> Relation<(T::Origin, T::Loan)> {
        let mut iteration = datafrog::Iteration::new();
        let known_contains = iteration.variable("known_contains");

        // known_contains(Origin1, Loan1) :-
        //   placeholder(Origin1, Loan1).
        known_contains.extend(placeholder.iter());

        while iteration.changed() {
            // known_contains(Origin2, Loan1) :-
            //   known_contains(Origin1, Loan1),
            //   known_subset(Origin1, Origin2).
            known_contains.from_join(
                &known_contains,
                known_subset,
                |&_origin1, &loan1, &origin2| (origin2, loan1),
            );
        }

        known_contains.complete()
    }

    fn new(dump_enabled: bool) -> Self {
        Output {
            errors: FxHashMap::default(),
            subset_errors: FxHashMap::default(),
            dump_enabled,
            borrow_live_at: FxHashMap::default(),
            restricts: FxHashMap::default(),
            restricts_anywhere: FxHashMap::default(),
            region_live_at: FxHashMap::default(),
            invalidates: FxHashMap::default(),
            subset: FxHashMap::default(),
            subset_anywhere: FxHashMap::default(),
            var_live_at: FxHashMap::default(),
            var_drop_live_at: FxHashMap::default(),
            path_maybe_initialized_at: FxHashMap::default(),
            var_maybe_initialized_on_exit: FxHashMap::default(),
            known_contains: FxHashMap::default(),
        }
    }

    pub fn errors_at(&self, location: T::Point) -> &[T::Loan] {
        match self.errors.get(&location) {
            Some(v) => v,
            None => &[],
        }
    }

    pub fn borrows_in_scope_at(&self, location: T::Point) -> &[T::Loan] {
        match self.borrow_live_at.get(&location) {
            Some(p) => p,
            None => &[],
        }
    }

    pub fn restricts_at(
        &self,
        location: T::Point,
    ) -> Cow<'_, BTreeMap<T::Origin, BTreeSet<T::Loan>>> {
        assert!(self.dump_enabled);
        match self.restricts.get(&location) {
            Some(map) => Cow::Borrowed(map),
            None => Cow::Owned(BTreeMap::default()),
        }
    }

    pub fn regions_live_at(&self, location: T::Point) -> &[T::Origin] {
        assert!(self.dump_enabled);
        match self.region_live_at.get(&location) {
            Some(v) => v,
            None => &[],
        }
    }

    pub fn subsets_at(
        &self,
        location: T::Point,
    ) -> Cow<'_, BTreeMap<T::Origin, BTreeSet<T::Origin>>> {
        assert!(self.dump_enabled);
        match self.subset.get(&location) {
            Some(v) => Cow::Borrowed(v),
            None => Cow::Owned(BTreeMap::default()),
        }
    }
}

/// Compares errors reported by Naive implementation with the errors
/// reported by the optimized implementation.
fn compare_errors<Loan: Atom, Point: Atom>(
    all_naive_errors: &FxHashMap<Point, Vec<Loan>>,
    all_opt_errors: &FxHashMap<Point, Vec<Loan>>,
) -> bool {
    let points = all_naive_errors.keys().chain(all_opt_errors.keys());

    let mut differ = false;
    for point in points {
        let mut naive_errors = all_naive_errors.get(&point).cloned().unwrap_or_default();
        naive_errors.sort();

        let mut opt_errors = all_opt_errors.get(&point).cloned().unwrap_or_default();
        opt_errors.sort();

        for err in naive_errors.iter() {
            if !opt_errors.contains(err) {
                error!(
                    "Error {0:?} at {1:?} reported by naive, but not opt.",
                    err, point
                );
                differ = true;
            }
        }

        for err in opt_errors.iter() {
            if !naive_errors.contains(err) {
                error!(
                    "Error {0:?} at {1:?} reported by opt, but not naive.",
                    err, point
                );
                differ = true;
            }
        }
    }

    differ
}

#[cfg(test)]
mod tests {
    use super::*;

    impl Atom for usize {
        fn index(self) -> usize {
            self
        }
    }

    fn compare(
        errors1: &FxHashMap<usize, Vec<usize>>,
        errors2: &FxHashMap<usize, Vec<usize>>,
    ) -> bool {
        let diff1 = compare_errors(errors1, errors2);
        let diff2 = compare_errors(errors2, errors1);
        assert_eq!(diff1, diff2);
        diff1
    }

    #[test]
    fn test_compare_errors() {
        let empty = FxHashMap::default();
        assert_eq!(false, compare(&empty, &empty));
        let mut empty_vec = FxHashMap::default();
        empty_vec.insert(1, vec![]);
        empty_vec.insert(2, vec![]);
        assert_eq!(false, compare(&empty, &empty_vec));

        let mut singleton1 = FxHashMap::default();
        singleton1.insert(1, vec![10]);
        assert_eq!(false, compare(&singleton1, &singleton1));
        let mut singleton2 = FxHashMap::default();
        singleton2.insert(1, vec![11]);
        assert_eq!(false, compare(&singleton2, &singleton2));
        let mut singleton3 = FxHashMap::default();
        singleton3.insert(2, vec![10]);
        assert_eq!(false, compare(&singleton3, &singleton3));

        assert_eq!(true, compare(&singleton1, &singleton2));
        assert_eq!(true, compare(&singleton2, &singleton3));
        assert_eq!(true, compare(&singleton1, &singleton3));

        assert_eq!(true, compare(&empty, &singleton1));
        assert_eq!(true, compare(&empty, &singleton2));
        assert_eq!(true, compare(&empty, &singleton3));

        let mut errors1 = FxHashMap::default();
        errors1.insert(1, vec![11]);
        errors1.insert(2, vec![10]);
        assert_eq!(false, compare(&errors1, &errors1));
        assert_eq!(true, compare(&errors1, &singleton1));
        assert_eq!(true, compare(&errors1, &singleton2));
        assert_eq!(true, compare(&errors1, &singleton3));
    }
}
