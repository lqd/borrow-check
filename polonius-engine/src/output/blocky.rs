use datafrog::{Iteration, Relation, RelationLeaper};
use std::time::Instant;

use crate::output::Output;
use crate::FactTypes;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
// use std::collections::BTreeSet;

/// Subset of `AllFacts` dedicated to borrow checking, and data ready to use by the variants
struct BlockyContext<'ctx, T: FactTypes> {
    // `Relation`s used as static inputs, by all variants
    region_live_at: &'ctx Relation<(T::Origin, T::Point)>,
    invalidates: &'ctx Relation<(T::Loan, T::Point)>,

    // static inputs used via `Variable`s, by all variants
    outlives: &'ctx FxHashSet<(T::Origin, T::Origin, T::Point)>,
    borrow_region: &'ctx FxHashSet<(T::Origin, T::Loan, T::Point)>,

    // static inputs used by variants other than `LocationInsensitive`
    // cfg_node: &'ctx BTreeSet<T::Point>,
    killed: &'ctx Relation<(T::Loan, T::Point)>,

    // known_contains: &'ctx Relation<(T::Origin, T::Loan)>,
    placeholder_origin: &'ctx Relation<(T::Origin, ())>,
    // placeholder_loan: &'ctx Relation<(T::Loan, T::Origin)>,

    // while this static input is unused by `LocationInsensitive`, it's depended on by initialization
    // and liveness, so already computed by the time we get to borrowcking.
    cfg_edge: &'ctx Relation<(T::Point, T::Point)>,

    known_subset: &'ctx Relation<(T::Origin, T::Origin)>,
}

struct BlockyResult<T: FactTypes> {
    errors: Relation<(T::Loan, T::Point)>,
    subset_errors: Relation<(T::Origin, T::Origin, T::Point)>,

    subset: Relation<(T::Origin, T::Origin, T::Point)>,
    requires: Relation<(T::Origin, T::Loan, T::Point)>,

    pub new_tuples: usize,
}

pub fn blockify_my_love<T: FactTypes>(
    facts: crate::AllFacts<T>,
    unterner: &dyn super::Unterner<T>,
    mut output: &mut Output<T>,
) {
    // function data
    // note: the `known_subset` relation in the facts does not necessarily contain its whole transitive closure,
    // so compute it.
    let known_subset = {
        let mut iteration = Iteration::new();

        let known_subset_base: Relation<_> = facts.known_subset.clone().into();
        let known_subset = iteration.variable("known_subset");

        // known_subset(Origin1, Origin2) :-
        //   known_subset_base(Origin1, Origin2).
        known_subset.extend(known_subset_base.iter());

        while iteration.changed() {
            // known_subset(Origin1, Origin3) :-
            //   known_subset(Origin1, Origin2),
            //   known_subset_base(Origin2, Origin3).
            known_subset.from_leapjoin(
                &known_subset,
                known_subset_base.extend_with(|&(_origin1, origin2)| origin2),
                |&(origin1, _origin2), &origin3| (origin1, origin3),
            );
        }

        known_subset.complete()
    };
    println!(
        "known_subset facts: {}, TC: {}",
        facts.known_subset.len(),
        known_subset.len()
    );

    // // The set of "interesting" loans
    // let interesting_loan: FxHashSet<_> = facts
    //     .invalidates
    //     .iter()
    //     .map(|&(_point, loan)| loan)
    //     .collect();
    // println!("interesting_loan: {}", interesting_loan.len());

    // // The "interesting" borrow regions are the ones referring to loans for which an error could occur
    // let interesting_borrow_region: FxHashSet<_> = facts
    //     .borrow_region
    //     .iter()
    //     .filter(|&(_origin, loan, _point)| interesting_loan.contains(loan))
    //     .copied()
    //     .collect();

    // // The interesting origins are:
    // // - for illegal access errors: any origin into which an interesting loan could flow.
    // // - for illegal subset relation errors: any placeholder origin. (TODO: this can likely
    // //   be tightened further to some of the placeholders which are _not_ in the
    // //   `known_subset` relation: they are the only ones into which an unexpected placeholder
    // //   loan can flow)
    // let (interesting_origin, interesting_placeholder) = {
    //     let mut iteration = Iteration::new();

    //     let outlives_o1 = Relation::from_iter(
    //         facts
    //             .outlives
    //             .iter()
    //             .map(|&(origin1, origin2, _point)| (origin1, origin2)),
    //     );

    //     let interesting_origin = iteration.variable::<(T::Origin, ())>("interesting_origin");
    //     let placeholder_origin_step1 =
    //         iteration.variable::<((T::Origin, T::Origin), ())>("placeholder_origin_step1");
    //     let placeholder_origin = iteration.variable::<(T::Origin, ())>("placeholder_origin");

    //     // interesting_origin(Origin) :-
    //     //   interesting_borrow_region(Origin, _, _);
    //     interesting_origin.extend(
    //         interesting_borrow_region
    //             .iter()
    //             .map(|&(origin, _loan, _point)| (origin, ())),
    //     );

    //     // interesting_origin(Origin) :-
    //     //   placeholder(Origin, _);
    //     interesting_origin.extend(
    //         facts
    //             .placeholder
    //             .iter()
    //             .map(|&(origin, _loan)| (origin, ())),
    //     );
    //     placeholder_origin.extend(
    //         facts
    //             .placeholder
    //             .iter()
    //             .map(|&(origin, _loan)| (origin, ())),
    //     );

    //     while iteration.changed() {
    //         // interesting_origin(Origin2) :-
    //         //   outlives(Origin1, Origin2, _),
    //         //   interesting_origin(Origin1, _, _);
    //         interesting_origin.from_join(
    //             &interesting_origin,
    //             &outlives_o1,
    //             |_origin1, (), &origin2| (origin2, ()),
    //         );

    //         // placeholder_origin(Origin2) :-
    //         //   placeholder_origin(Origin1, _, _),
    //         //   outlives(Origin1, Origin2, _),
    //         //   !known_subset(Origin1, Origin2);
    //         placeholder_origin_step1.from_join(
    //             &placeholder_origin,
    //             &outlives_o1,
    //             |&origin1, (), &origin2| ((origin1, origin2), ()),
    //         );
    //         placeholder_origin.from_antijoin(
    //             &placeholder_origin_step1,
    //             &known_subset,
    //             |&(_origin1, origin2), ()| (origin2, ()),
    //         );
    //     }

    //     (
    //         interesting_origin
    //             .complete()
    //             .iter()
    //             .map(|&(origin1, _)| origin1)
    //             .collect::<FxHashSet<_>>(),
    //         placeholder_origin
    //             .complete()
    //             .iter()
    //             .map(|&(origin1, _)| origin1)
    //             .collect::<FxHashSet<_>>()
    //     )
    // };

    // println!("interesting_origin: {}", interesting_origin.len());
    // println!("interesting_placeholder: {}", interesting_placeholder.len());

    // block data

    let block_from_point = |point| {
        let point = unterner.untern_point(point);

        // point naming pattern:
        // - "Mid(bb0[12])" from rustc generated facts,
        // - "Mid(B0[12])" from polonius unit tests

        let point_type_separator = point.find('(').unwrap();
        let point_block_separator = point.find('[').unwrap();

        let block = &point[point_type_separator + 1..point_block_separator];

        let block_idx_pos = block.chars().position(|c| c.is_numeric()).unwrap();
        let block_idx = &block[block_idx_pos..];
        (point, block_idx.parse::<usize>().unwrap())
    };

    let mut block_borrow_region: FxHashMap<usize, FxHashSet<(T::Origin, T::Loan, T::Point)>> =
        Default::default();
    let mut xxx = 0;
    for fact in facts.borrow_region.iter() {
        let (_point, block_idx) = block_from_point(fact.2);
        // println!("borrow_region {:?} is from {} block {}", fact, point, block_idx);

        // interestingness filter
        // if !interesting_borrow_region.contains(&fact) {
        //     continue;
        // }

        xxx += 1;

        block_borrow_region
            .entry(block_idx)
            .or_default()
            .insert(*fact);
    }

    // println!("block_borrow_region done");
    println!(
        "block_borrow_region done, {} / {}",
        xxx,
        facts.borrow_region.len()
    );

    // facts.universal_region has no points

    let mut block_cfg_edge: FxHashMap<usize, FxHashSet<(T::Point, T::Point)>> = Default::default();

    let mut block_terminator_predecessor: FxHashMap<T::Point, FxHashSet<usize>> =
        Default::default();
    let mut block_terminator_successor: FxHashMap<T::Point, FxHashSet<usize>> = Default::default();

    let mut block_successor: FxHashMap<usize, FxHashSet<usize>> = Default::default();

    for fact in facts.cfg_edge.iter() {
        let (_point_from, block_from_idx) = block_from_point(fact.0);
        let (_point_to, block_to_idx) = block_from_point(fact.1);
        // println!("cfg_edge {:?} is from {} block {}, to {} block {}", fact, _point_from, block_from_idx, _point_to, block_to_idx);

        // check if we need the predecessors -> block start point edges in the CFG
        // we need it in liveness propagation for sure
        block_cfg_edge
            .entry(block_from_idx)
            .or_default()
            .insert(*fact);

        if block_from_idx != block_to_idx {
            block_cfg_edge
                .entry(block_to_idx)
                .or_default()
                .insert(*fact);
        }

        // if this a block terminator edge, record from/to blocks as the block interface edges
        if block_from_idx != block_to_idx {
            // println!("terminator cfg_edge {:?} is from {} block {}, to {} block {}", fact, _point_from, block_from_idx, _point_to, block_to_idx);
            block_terminator_predecessor
                .entry(fact.1)
                .or_default()
                .insert(block_from_idx);
            block_terminator_successor
                .entry(fact.0)
                .or_default()
                .insert(block_to_idx);

            block_successor
                .entry(block_from_idx)
                .or_default()
                .insert(block_to_idx);
        }
    }

    println!("block_cfg_edge done: {}", facts.cfg_edge.len());

    let mut block_killed: FxHashMap<usize, FxHashSet<(T::Loan, T::Point)>> = Default::default();
    for fact in facts.killed.iter() {
        let (_point, block_idx) = block_from_point(fact.1);
        // println!("killed {:?} is from {} block {}", fact, _point, block_idx);

        block_killed.entry(block_idx).or_default().insert(*fact);
    }

    println!("block_killed done: {}", facts.killed.len());

    let mut block_outlives: FxHashMap<usize, FxHashSet<(T::Origin, T::Origin, T::Point)>> =
        Default::default();
    let mut xxx = 0;
    for fact in facts.outlives.iter() {
        let (_point, block_idx) = block_from_point(fact.2);
        // println!("outlives {:?} is from {} block {}", fact, point, block_idx);

        // interestingness filter
        // if !interesting_origin.contains(&fact.0) && !interesting_placeholder.contains(&fact.0) {
        //     continue;
        // }

        xxx += 1;

        block_outlives.entry(block_idx).or_default().insert(*fact);
    }

    // println!("block_outlives done");
    println!("block_outlives done: {} / {}", xxx, facts.outlives.len());

    let mut block_invalidates: FxHashMap<usize, FxHashSet<(T::Point, T::Loan)>> =
        Default::default();
    for fact in facts.invalidates.iter() {
        let (_point, block_idx) = block_from_point(fact.0);
        // println!("invalidates {:?} is from {} block {}", fact, _point, block_idx);

        block_invalidates
            .entry(block_idx)
            .or_default()
            .insert(*fact);
    }

    println!("block_invalidates done: {}", facts.invalidates.len());

    ///////////////////
    // Step 1 - Index the CFG to find the eligible points matching the requirements,
    // and make the sets of live regions at each point easily comparable.
    let mut successors = FxHashMap::default();
    let mut predecessors = FxHashMap::default();

    use std::collections::hash_map::Entry;

    let xxxx_edge_count = facts.cfg_edge.len();

    for &(p, q) in &facts.cfg_edge {
        match successors.entry(p) {
            Entry::Vacant(entry) => {
                entry.insert(Some(q));
            }
            Entry::Occupied(mut entry) => {
                let successor = entry.get_mut();
                if successor.is_some() {
                    // There is already a successor: this point can't be compressed
                    *successor = None;
                }
            }
        }

        match predecessors.entry(q) {
            Entry::Vacant(entry) => {
                entry.insert(Some(p));
            }

            Entry::Occupied(mut entry) => {
                let predecessor = entry.get_mut();
                if predecessor.is_some() {
                    // There is already a predecessor: this point can't be compressed
                    *predecessor = None;
                }
            }
        }
    }

    let mut xoutlives = FxHashMap::default();
    for (o1, o2, p) in &facts.outlives {
        xoutlives
            .entry(*p)
            .or_insert_with(FxHashSet::default)
            .insert((*o1, *o2));
    }

    let mut xkilled = FxHashMap::default();
    for &(l, p) in &facts.killed {
        xkilled
            .entry(p)
            .or_insert_with(FxHashSet::default)
            .insert(l);
    }

    let mut xinvalidates = FxHashMap::default();
    for &(p, l) in &facts.invalidates {
        xinvalidates
            .entry(p)
            .or_insert_with(FxHashSet::default)
            .insert(l);
    }

    ///////////////////

    let mut yycfg_edge = facts.cfg_edge.clone();

    // function data
    let (_known_contains, placeholder_origin, _placeholder_loan, region_live_at, universal_regions) =
        create_function_data(facts, &mut output);
    println!("function data computed");

    //////////
    let mut xregion_live_at = FxHashMap::default();
    for &(r, p) in &region_live_at {
        xregion_live_at
            .entry(p)
            .or_insert_with(FxHashSet::default)
            .insert(r);
    }

    // Step 2 - Locate eligible points
    let mut compressed_points = FxHashSet::default();
    let mut compressible_edges = Vec::new();

    for (p, q) in successors.into_iter() {
        // Compressible points have only one outgoing edge.
        //
        // Note: it could be interesting to investigate the impact of contracting acceptable
        // children edges into `p`'s parent : in the graph `(a, b), (b, c), (b, d)`
        // contracting `b` away would require additional constraints between `c`, `d` and `a`.
        // However, in early tests of our datasets, the number of cases where all children edges
        // had the same set of live regions as their parent seemed small (e.g for clap, for 49K total
        // points: 3275 points had more than one child node, with 231 having the same live regions).
        // There might be rules specific to multiple-children cases but they probably aren't the same as the
        // single-child node cases implemented here.

        let q = match q {
            None => continue, // more than one successor
            Some(successor) => successor,
        };

        let (_x, block_x_idx) = block_from_point(p);
        let (_y, block_y_idx) = block_from_point(q);
        
        use facts::Atom;
        if block_x_idx == 0 && p.index() == 1316 {
            println!("point p: {} - predecessors: {:?}", _x, predecessors.get(&p));
        }

        if block_y_idx == 0 && q.index() == 1316 {
            println!("point q: {} - predecessors: {:?}", _y, predecessors.get(&q));
        }

        if block_x_idx != block_y_idx {
            continue; // no inter-block compression
        }

        // Compressible points have only one incoming edge, and as the the point `p` is merged
        // into its parent's edge, the root edge can't be contracted.
        match predecessors.get(&q) {
            None => {  println!("point {:?} is the root", q); continue },       // root node
            Some(None) => continue, // more than one predecessor
            Some(Some(_)) => {}
        }

        // Compressible points have the same live regions.
        if xregion_live_at.get(&p) != xregion_live_at.get(&q) {
            continue;
        }

        // let a = xoutlives.get(&p);
        // let b = xoutlives.get(&q);
        // match (a, b) {
        //     (Some(x), _) if !x.is_empty() => continue,
        //     (_, Some(x)) if !x.is_empty() => continue,
        //     _ => {}
        // }

        if xoutlives.get(&p) != xoutlives.get(&q) {
            continue;
        }

        // let a = xkilled.get(&p);
        // let b = xkilled.get(&q);
        // match (a, b) {
        //     (Some(x), _) if !x.is_empty() => continue,
        //     (_, Some(x)) if !x.is_empty() => continue,
        //     _ => {}
        // }

        if xkilled.get(&p) != xkilled.get(&q) {
            continue;
        }

        // if xinvalidates.get(&p) != xinvalidates.get(&q) {
        //     continue;
        // }

        // let a = xinvalidates.get(&p);
        // let b = xinvalidates.get(&q);
        // match (a, b) {
        //     (Some(x), _) if !x.is_empty() => continue,
        //     (_, Some(x)) if !x.is_empty() => continue,
        //     _ => {}
        // }

        // Note: as only `invalidates` points can be the source of errors, more investigation
        // could be done to see whether there is more compression and filtering opportunities
        // there: the important points will contribute to liveness while not being error
        // sources.

        if block_x_idx + block_y_idx == 0 {
            println!("point {} is compressible", _x);
        }

        compressible_edges.push((p, q));
        compressed_points.insert(p);
    }

    println!("compressible_edges: {} / {}", compressible_edges.len(), xxxx_edge_count);
    println!("compressed points: {}", compressed_points.len());

    // Step 3 - Compute the CFG compression
    // - Propagate the previously located points along compressed edges until reaching the
    //   important point at the end of the chain.
    // - Record these vertex contractions in an equivalence table: the edges from compressed
    //   points to non-compressed points necessary to decompress the live borrows which could
    //   be computed at these important points.
    let equivalence_table = {
        let mut iteration = Iteration::new();

        let compression_table = iteration.variable("compression_table");
        let compressed_edge = iteration.variable_indistinct("compressed_edge");

        let compressed_point = Relation::from_iter(compressed_points.iter().cloned());

        let propagated_edge_q = iteration.variable("propagated_edge_q");
        propagated_edge_q.insert(Relation::from_iter(
            compressible_edges.iter().map(|&(p, q)| (q, p)),
        ));

        compressed_edge.insert(compressible_edges.into());

        while iteration.changed() {
            // propagated_edge(P, Q) :- compressed_edge(P, Q);
            // -> already done at loading time for a static input

            // propagated_edge(P, R) :-
            //     propagated_edge(P, Q),
            //     compressed_edge(Q, R).
            propagated_edge_q
                .from_join(&propagated_edge_q, &compressed_edge, |&_q, &p, &r| (r, p));

            // compression_table(P, Q) :-
            //     propagated_edge(P, Q),
            //     !compressed_point(Q).
            compression_table
                .from_antijoin(&propagated_edge_q, &compressed_point, |&q, &p| (p, q));
        }

        let mut equivalence_table = FxHashMap::default();
        for &(p, q) in compression_table.complete().iter() {
            equivalence_table.insert(p, q);
        }

        equivalence_table
    };

    for fact in yycfg_edge.iter() {
        let (_point_from, block_from_idx) = block_from_point(fact.0);
        let (_point_to, block_to_idx) = block_from_point(fact.1);
        if block_from_idx == 0 || block_to_idx == 0 {
            println!("A - yycfg_edge {:?} is from {} block {}, to {} block {}", fact, _point_from, block_from_idx, _point_to, block_to_idx);
        }
    }

    // Step 4 - Contract the CFG according to the edges' contribution to `subset`s:
    // 1) edges between important points: keep them as-is, they contribute to `subset`s
    // 2) edges from compressible points: contract them away, they don't contribute to
    //   `subset`s.
    // 3) edges from an important point to a compressible point: propagated from the source to
    //    its eventual destination (an important point), potentially through a chain of compressible
    //    points.
    //    For example, e1: (p, q), e2 (q, r), e3 (r, s) where `q` and `r` are compressible, and
    //    `q`, `r`, and `s` have equivalent contributions to `subset`s.
    //    - e2 and e3 will be removed by rule #2.
    //    - we keep the same liveness differences by connecting the source and destination
    //      of the chain: (p, s)
    //
    for i in (0..yycfg_edge.len()).rev() {
        let (p, q) = yycfg_edge[i];
        let (_point_from, a) = block_from_point(p);
        let (_point_to, b) = block_from_point(q);
        if compressed_points.contains(&p) {
            if a == 0 || b == 0 {
                println!("removing edge {} -> {} as {} was compressed away", _point_from, _point_to, _point_from);
            }
            yycfg_edge.swap_remove(i);
        } else {
            if compressed_points.contains(&q) {
                if a == 0 || b == 0 {
                    let (to, _) = block_from_point(equivalence_table[&q]);
                    println!("contracting edge {} -> {} into {} -> {}", _point_from, _point_to, _point_from, to);
                }
                yycfg_edge[i].1 = equivalence_table[&q];
            }
        }
    }
    println!("yycfg_edge: {} / {}", yycfg_edge.len(), xxxx_edge_count);

    for fact in yycfg_edge.iter() {
        let (_point_from, block_from_idx) = block_from_point(fact.0);
        let (_point_to, block_to_idx) = block_from_point(fact.1);
        if block_from_idx == 0 || block_to_idx == 0 {
            println!("B - yycfg_edge {:?} is from {} block {}, to {} block {}", fact, _point_from, block_from_idx, _point_to, block_to_idx);
        }
    }

    std::process::exit(0);

    /////////

    // liveness block data
    let mut block_region_live_at: FxHashMap<usize, FxHashSet<(T::Origin, T::Point)>> =
        Default::default();
    let mut xxx = 0;
    let yyy = region_live_at.len();
    for fact in region_live_at.into_iter() {
        let (_point, block_idx) = block_from_point(fact.1);

        // Interestingness filter (should be uplifted to liveness itself as usual, this is just a test)
        // if !interesting_origin.contains(&fact.0) {
        //     continue;
        // }

        xxx += 1;

        // println!("region_live_at {:?} is from {} block {}", fact, _point, block_idx);

        block_region_live_at
            .entry(block_idx)
            .or_default()
            .insert(fact);

        if let Some(successor_blocks) = block_terminator_successor.get(&fact.1) {
            for &successor_block in successor_blocks {
                // println!("region_live_at {:?} is from {} which is an edge to successor block {}", fact, _point, successor_block);
                block_region_live_at
                    .entry(successor_block)
                    .or_default()
                    .insert(fact);
            }
        }

        if let Some(predecessor_blocks) = block_terminator_predecessor.get(&fact.1) {
            for &predecessor_block in predecessor_blocks {
                // println!("region_live_at {:?} is from {} which is an edge to predecessor block {}", fact, _point, predecessor_block);
                block_region_live_at
                    .entry(predecessor_block)
                    .or_default()
                    .insert(fact);
            }
        }
    }

    let block_count = block_cfg_edge.keys().len();

    // for block_idx in 0..block_count {
    //     block_region_live_at.entry(block_idx).or_default().extend(region_live_at.iter());
    // }

    println!("block_region_live_at done: {}, {}", xxx, yyy);

    struct BlockContext<T: FactTypes> {
        region_live_at: Relation<(T::Origin, T::Point)>,
        invalidates: Relation<(T::Loan, T::Point)>,

        outlives: FxHashSet<(T::Origin, T::Origin, T::Point)>,
        borrow_region: FxHashSet<(T::Origin, T::Loan, T::Point)>,

        // cfg_node: BTreeSet<T::Point>,
        killed: Relation<(T::Loan, T::Point)>,

        cfg_edge: Relation<(T::Point, T::Point)>,
    }

    let mut block_facts: FxHashMap<usize, BlockContext<T>> = Default::default();
    for block_idx in 0..block_count {
        let invalidates = block_invalidates.remove(&block_idx).unwrap_or_default();

        // TODO: filtrer les 3 relations suivantes pour ne traquer que les loans et origins intéressants
        let mut region_live_at: Vec<_> = block_region_live_at
            .remove(&block_idx)
            .unwrap_or_default()
            .into_iter()
            .collect();

        let borrow_region = block_borrow_region.remove(&block_idx).unwrap_or_default();

        let outlives = block_outlives.remove(&block_idx).unwrap_or_default();

        // TODO: cfg compression
        let cfg_edge: Vec<_> = block_cfg_edge
            .remove(&block_idx)
            .unwrap_or_default()
            .into_iter()
            .collect();

        let killed: Vec<_> = block_killed
            .remove(&block_idx)
            .unwrap_or_default()
            .into_iter()
            .collect();

        let invalidates =
            Relation::from_iter(invalidates.iter().map(|&(point, loan)| (loan, point)));

        let cfg_node = cfg_edge
            .iter()
            .map(|&(point1, _)| point1)
            .chain(cfg_edge.iter().map(|&(_, point2)| point2))
            .collect();

        super::liveness::make_universal_regions_live::<T>(
            &mut region_live_at,
            &cfg_node,
            &universal_regions,
        );

        let ctx = BlockContext {
            region_live_at: region_live_at.into(),

            borrow_region,
            outlives,

            cfg_edge: cfg_edge.into(),
            // cfg_node,
            killed: killed.into(),
            invalidates: invalidates.into(),
        };

        block_facts.insert(block_idx, ctx);
    }

    println!("block_count: {}", block_facts.len());

    let timer = Instant::now();

    // TODO: maybe order the CFG better, eg a BFS here ?
    let mut blocks: VecDeque<_> = (0..block_count).collect();
    // println!("queue: {:?}", blocks.iter().take(10).collect::<Vec<_>>());

    println!("");

    let mut count = 0;
    while let Some(block_idx) = blocks.pop_front() {
        count += 1;

        if count > 100_000 {
            println!("\n\nnope, bailing out after too many iterations");
            break;
        }

        // println!("current block: {}", block_idx);
        // println!("current block: {} / iteration: {}", block_idx, count);
        // println!("block to visit: {} - queue: {:?}", block_idx, blocks.iter().take(5).collect::<Vec<_>>());
        // println!("block to visit: {} - queue: {:?}", block_idx, blocks.len());

        let bb_facts = block_facts.get(&block_idx).unwrap();

        // TODO: no invalidations means there can be no illegal access error here. Apart from
        // subset errors, and transporting loans across edges, part of the analysis can be avoided.
        // if bb_facts.invalidates.is_empty() {
        //     continue;
        // }
        // println!("current block: {} - invalidates: {}", block_idx, bb_facts.invalidates.len());

        // TODO: we can probably have cases with shortcuts to transport information directly to the next block
        // without needing to have a discrete step for each edge via the full analysis. At the very least CFG compression
        // is equally applicable here.

        // TODO: other interesting case: no regions are live in a block

        // if block_idx == 2139 {
        //     println!();
        //     println!("current block: {} / iteration: {}", block_idx, count);
        //     println!("bb {} - input to subset / outlives: {:?}", block_idx, bb_facts.outlives.len());
        // }

        let ctx = BlockyContext::<T> {
            known_subset: &known_subset,
            placeholder_origin: &placeholder_origin,
            // placeholder_loan: &placeholder_loan,
            // known_contains: &known_contains,
            cfg_edge: &bb_facts.cfg_edge,
            region_live_at: &bb_facts.region_live_at,
            borrow_region: &bb_facts.borrow_region,
            outlives: &bb_facts.outlives,
            // cfg_node: &bb_facts.cfg_node,
            killed: &bb_facts.killed,
            invalidates: &bb_facts.invalidates,
        };

        // let timer = Instant::now();
        let result = compute(&ctx, output, unterner);
        // let elapsed = timer.elapsed();

        // println!("new tuples: {:?}", result.new_tuples);
        // println!("errors: {:?}", result.errors.elements);

        if result.errors.len() > 0 {
            println!("\n");
            for error in result.errors.iter() {
                println!(
                    "found an error, {:?}, at {}",
                    error,
                    unterner.untern_point(error.1)
                );
            }
            println!("\n");

            for &(loan, location) in result.errors.iter() {
                output.errors.entry(location).or_default().push(loan);
            }
        }

        if result.subset_errors.len() > 0 {
            println!("\n");
            for error in result.subset_errors.iter() {
                println!(
                    "found a subset error, {:?}, {} flows into {} at {}",
                    error,
                    unterner.untern_origin(error.0),
                    unterner.untern_origin(error.1),
                    unterner.untern_point(error.2),
                );
            }
            println!("\n");

            for &(origin1, origin2, location) in result.subset_errors.iter() {
                output
                    .subset_errors
                    .entry(location)
                    .or_default()
                    .insert((origin1, origin2));
            }
        }

        // if block_idx == 2138 || block_idx == 2139 {
        // if block_idx == 2139 {
        //     println!();
        //     println!("current block: {} / iteration: {} / duration: {:?}", block_idx, count, elapsed);
        //     println!("bb {} - new tuples: {:?}", block_idx, result.new_tuples);
        //     println!("bb {} - input to subset / outlives: {:?}", block_idx, bb_facts.outlives.len());
        //     println!("bb {} - input to requires / borrow_region: {:?}", block_idx, bb_facts.borrow_region.len());
        //     println!("bb {} - result subset: {:?}", block_idx, result.subset.len());
        //     println!("bb {} - result requires: {:?}", block_idx, result.requires.len());
        //     println!();
        // }

        // if we're not at a local fixpoint yet
        if result.new_tuples > 0 {
            if let Some(successor_blocks) = block_successor.get(&block_idx) {
                // println!("block {} to: {:?} - queue pre-merging: {:?}", block_idx, successor_blocks, blocks.iter().take(5).collect::<Vec<_>>());

                for &successor_block_idx in successor_blocks {
                    // if successor_block_idx == 2139 {
                    //     println!("merging current block {}, with successor block {}", block_idx, successor_block_idx);
                    // }

                    // println!("merging current block {}, with successor block {}", block_idx, successor_block_idx);
                    let successor_facts = block_facts.get_mut(&successor_block_idx).unwrap();

                    // merge requires / subsets at the block interface: the new block needs to know only the new facts
                    // at its entry point

                    // for fact in result.subset.iter() {
                    //     let (_point, local_block_idx) = block_from_point(fact.2);
                    //     if local_block_idx == successor_block_idx {
                    //         println!("merging 'subset' {:?} at {} from block {}, with block {}", fact, _point, block_idx, successor_block_idx);
                    //     }
                    // }

                    let successor_outlives = successor_facts.outlives.len();
                    let successor_borrow_regions = successor_facts.borrow_region.len();

                    successor_facts
                        .outlives
                        .extend(result.subset.iter().filter(|fact| {
                            let (_, local_block_idx) = block_from_point(fact.2);
                            local_block_idx == successor_block_idx
                        }));

                    // for fact in result.requires.iter() {
                    //     let (_point, local_block_idx) = block_from_point(fact.2);
                    //     if local_block_idx == successor_block_idx {
                    //         println!("merging 'requires' {:?} at {} from block {}, with block {}", fact, _point, block_idx, successor_block_idx);
                    //     }
                    // }

                    successor_facts
                        .borrow_region
                        .extend(result.requires.iter().filter(|fact| {
                            let (_, local_block_idx) = block_from_point(fact.2);
                            local_block_idx == successor_block_idx
                        }));

                    // we tried merging the result tuples in the successor blocks. if the tuple count didn't change, then re-running
                    // the computation on the successor would result in a result we already have. We're already at a fixpoint state for
                    // the successor block.

                    let new_outlives_facts = successor_facts.outlives.len() != successor_outlives;
                    let new_borrow_region_facts =
                        successor_facts.borrow_region.len() != successor_borrow_regions;
                    let is_successor_dirty = new_outlives_facts || new_borrow_region_facts;

                    // if successor_block_idx == 2139 {
                    //     println!("from block: {} - is successor {} dirty: {}", block_idx, successor_block_idx, is_successor_dirty);
                    //     // dbg!(new_outlives_facts, new_borrow_region_facts);
                    // }

                    if is_successor_dirty {
                        if let Some(idx) = blocks.iter().position(|&e| e == successor_block_idx) {
                            blocks.remove(idx).unwrap();
                            blocks.insert(0, successor_block_idx);
                        } else {
                            blocks.push_front(successor_block_idx);
                        }
                    }
                }

                // println!("block {} to: {:?} - queue: {:?}", block_idx, successor_blocks, blocks.iter().take(5).collect::<Vec<_>>());
                // println!("block {} to: {:?}", block_idx, successor_blocks);
            }
        }
    }

    println!(
        "\nblocky elapsed: {:?}, took {} iterations",
        timer.elapsed(),
        count
    );
}

fn create_function_data<T: FactTypes>(
    all_facts: crate::AllFacts<T>,
    mut result: &mut Output<T>,
) -> (
    Relation<(T::Origin, T::Loan)>,
    Relation<(T::Origin, ())>,
    Relation<(T::Loan, T::Origin)>,
    Vec<(T::Origin, T::Point)>,
    Vec<T::Origin>,
) {
    use super::initialization;
    use super::liveness;
    use super::{InitializationContext, LivenessContext};

    let cfg_edge = all_facts.cfg_edge.into();

    // 1) Initialization
    let initialization_ctx = InitializationContext {
        child: all_facts.child,
        path_belongs_to_var: all_facts.path_belongs_to_var,
        initialized_at: all_facts.initialized_at,
        moved_out_at: all_facts.moved_out_at,
        path_accessed_at: all_facts.path_accessed_at,
    };

    let var_maybe_initialized_on_exit = initialization::init_var_maybe_initialized_on_exit(
        initialization_ctx,
        &cfg_edge,
        &mut result,
    );

    // 2) Liveness
    let liveness_ctx = LivenessContext {
        var_used: all_facts.var_used,
        var_defined: all_facts.var_defined,
        var_drop_used: all_facts.var_drop_used,
        var_uses_region: all_facts.var_uses_region,
        var_drops_region: all_facts.var_drops_region,
    };

    let region_live_at = liveness::compute_live_regions(
        liveness_ctx,
        &cfg_edge,
        var_maybe_initialized_on_exit,
        &mut result,
    );

    let known_subset = all_facts.known_subset.into();
    let known_contains = Output::<T>::compute_known_contains(&known_subset, &all_facts.placeholder);

    let placeholder_origin: Relation<_> = Relation::from_iter(
        all_facts
            .universal_region
            .iter()
            .map(|&origin| (origin, ())),
    );

    let placeholder_loan = Relation::from_iter(
        all_facts
            .placeholder
            .iter()
            .map(|&(origin, loan)| (loan, origin)),
    );

    (
        known_contains,
        placeholder_origin,
        placeholder_loan,
        region_live_at,
        all_facts.universal_region,
    )
}

fn compute<T: FactTypes>(
    ctx: &BlockyContext<T>,
    _result: &mut Output<T>,
    _unterner: &dyn super::Unterner<T>,
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
    let region_live_at_var = iteration.variable::<((T::Origin, T::Point), ())>("region_live_at");

    // output relations: illegal accesses errors, and illegal subset relations errors
    let errors = iteration.variable("errors");
    let subset_errors = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset_errors");

    let subset_placeholder =
        iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset_placeholder");
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

    // // let placeholder_loans_count = placeholder_loans.len();
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
        //     placeholder_origin(Origin1).
        subset_placeholder.from_leapjoin(
            &subset,
            (
                placeholder_origin.extend_with(|&(origin1, _origin2, _point)| origin1),
                // remove symmetries:
                datafrog::ValueFilter::from(|&(origin1, origin2, _point), ()| origin2 != origin1),
            ),
            |&(origin1, origin2, point), _| (origin1, origin2, point),
        );

        // subset_placeholder(Origin1, Origin3, Point) :-
        //     subset_placeholder(Origin1, Origin2, Point),
        //     subset(Origin2, Origin3, Point).
        subset_placeholder.from_join(
            &subset_placeholder_o2p,
            &subset_o1p,
            |&(_origin2, point), &origin1, &origin3| (origin1, origin3, point),
        );

        // subset_error(Origin1, Origin2, Point) :-
        //     subset_placeholder(Origin1, Origin2, Point),
        //     placeholder_origin(Origin2),
        //     !known_subset(Origin1, Origin2).
        subset_errors.from_leapjoin(
            &subset_placeholder,
            (
                placeholder_origin.extend_with(|&(_origin1, origin2, _point)| origin2),
                known_subset.filter_anti(|&(origin1, origin2, _point)| (origin1, origin2)),
                // remove symmetries:
                datafrog::ValueFilter::from(|&(origin1, origin2, _point), ()| origin2 != origin1),
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
    // // println!("placeholder_loans: {}", placeholder_loans_count);

    // let subset_placeholder = subset_placeholder.complete();
    // println!("subset_placeholder: {}", subset_placeholder.len());

    // the new tuples are
    // - the number of new subsets (subsets at the end of the computation minus the initial value)
    // - the number of new requires (requires at the end of the computation minus the initial value)
    let new_tuples = subset.len() - ctx.outlives.len() + requires.len() - ctx.borrow_region.len();

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
