mod dump;
mod facts;
mod intern;
mod program;
mod tab_delim;
mod test;
mod test_util;

mod blocky;
pub mod cli;

use std::error::Error;
use std::path::Path;

use crate::dump::Output;
use crate::facts::{AllFacts, Loan, Origin, Point};
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;

use datafrog::Relation;
use std::collections::BTreeSet;
use std::collections::VecDeque;
use std::time::Instant;

pub fn blocky() -> Result<(), Box<dyn Error>> {
    let facts_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("inputs")
        .join("smoke-test")
        .join("nll-facts")
        .join("well_formed_function_inputs");

    // let facts_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
    //     .join("inputs")
    //     .join("vec-push-ref")
    //     .join("nll-facts")
    //     .join("foo1");

    // let facts_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
    //     .join("inputs")
    //     .join("clap-rs")
    //     .join("app-parser-{{impl}}-add_defaults");

    // TODO: check that facts are not lost at the interface between 2 blocks
    // for this example there's an edge from mid bb7.7 to bb9, verify that eg the
    // requires facts are 1) computed at the edge, 2) transported along this edge,
    // so that the computation is correct in bb9
    // bb9 is weird anyway here, maybe an unwind/false/imaginary edge
    // -> check this for other blocks as well, but eg bb13 to 14 is correct

    let mut tables = intern::InternerTables::new();
    let facts = tab_delim::load_tab_delimited_facts(&mut tables, &facts_dir)?;

    // function data
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
    // println!("facts borrow_region: {}, interesting_borrow_region: {}", facts.borrow_region.len(), interesting_borrow_region.len());

    // // The interesting origins are:
    // // - for illegal access errors: any origin into which an interesting loan could flow.
    // // - for illegal subset relation errors: any placeholder origin. (TODO: this can likely
    // //   be tightened further to some of the placeholders which are _not_ in the
    // //   `known_subset` relation: they are the only ones into which an unexpected placeholder
    // //   loan can flow)
    // let interesting_origin = {
    //     use datafrog::Iteration;

    //     let mut iteration = Iteration::new();

    //     let outlives_o1 = Relation::from_iter(
    //         facts
    //             .outlives
    //             .iter()
    //             .map(|&(origin1, origin2, _point)| (origin1, origin2)),
    //     );

    //     let interesting_origin = iteration.variable::<(Origin, ())>("interesting_origin");

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

    //     while iteration.changed() {
    //         // interesting_origin(Origin2) :-
    //         //   outlives(Origin1, Origin2, _),
    //         //   interesting_origin(Origin1, _, _);
    //         interesting_origin.from_join(
    //             &interesting_origin,
    //             &outlives_o1,
    //             |_origin1, (), &origin2| (origin2, ()),
    //         );
    //     }

    //     interesting_origin
    //         .complete()
    //         .iter()
    //         .map(|&(origin1, _)| origin1)
    //         .collect::<FxHashSet<_>>()
    // };

    // println!("interesting_origin: {}", interesting_origin.len());

    // block data

    let block_from_point = |point| {
        let point = tables.points.untern(point);

        // pattern: Mid(bb0[12])
        let point_type_separator = point.find('(').unwrap();
        let point_block_separator = point.find('[').unwrap();

        let block = &point[point_type_separator + 1..point_block_separator];
        let block_idx = &block[2..];
        (point, block_idx.parse::<usize>().unwrap())
    };

    let mut block_borrow_region: FxHashMap<usize, FxHashSet<(Origin, Loan, Point)>> =
        Default::default();
    for fact in facts.borrow_region.iter() {
        let (_point, block_idx) = block_from_point(fact.2);
        // println!("borrow_region {:?} is from {} block {}", fact, point, block_idx);

        // interestingness filter
        // if !interesting_borrow_region.contains(&fact) {
        //     continue;
        // }

        block_borrow_region
            .entry(block_idx)
            .or_default()
            .insert(*fact);
    }

    println!("block_borrow_region done");

    // facts.universal_region has no points

    let mut block_cfg_edge: FxHashMap<usize, FxHashSet<(Point, Point)>> = Default::default();

    let mut block_terminator_predecessor: FxHashMap<Point, FxHashSet<usize>> = Default::default();
    let mut block_terminator_successor: FxHashMap<Point, FxHashSet<usize>> = Default::default();

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

    println!("block_cfg_edge done");

    let mut block_killed: FxHashMap<usize, FxHashSet<(Loan, Point)>> = Default::default();
    for fact in facts.killed.iter() {
        let (_point, block_idx) = block_from_point(fact.1);
        // println!("killed {:?} is from {} block {}", fact, point, block_idx);

        block_killed.entry(block_idx).or_default().insert(*fact);
    }

    println!("block_killed done");

    let mut block_outlives: FxHashMap<usize, FxHashSet<(Origin, Origin, Point)>> =
        Default::default();
    for fact in facts.outlives.iter() {
        let (_point, block_idx) = block_from_point(fact.2);
        // println!("outlives {:?} is from {} block {}", fact, point, block_idx);

        // interestingness filter
        // if !interesting_origin.contains(&fact.0) {
        //     continue;
        // }

        block_outlives.entry(block_idx).or_default().insert(*fact);
    }

    println!("block_outlives done");

    let mut block_invalidates: FxHashMap<usize, FxHashSet<(Point, Loan)>> = Default::default();
    for fact in facts.invalidates.iter() {
        let (_point, block_idx) = block_from_point(fact.0);
        // println!("invalidates {:?} is from {} block {}", fact, point, block_idx);

        block_invalidates
            .entry(block_idx)
            .or_default()
            .insert(*fact);
    }

    println!("block_invalidates done");

    // function data

    let (known_contains, placeholder_origin, placeholder_loan, region_live_at) =
        create_function_data(facts);
    println!("function data computed");

    // liveness block data
    let mut block_region_live_at: FxHashMap<usize, FxHashSet<(Origin, Point)>> = Default::default();
    for fact in region_live_at.into_iter() {
        let (_point, block_idx) = block_from_point(fact.1);

        // Interestingness filter (should be uplifted to liveness itself as usual, this is just a test)
        // if !interesting_origin.contains(&fact.0) {
        //     continue;
        // }

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

    println!("block_region_live_at done");

    struct BlockContext {
        region_live_at: Relation<(Origin, Point)>,
        invalidates: Relation<(Loan, Point)>,

        outlives: FxHashSet<(Origin, Origin, Point)>,
        borrow_region: FxHashSet<(Origin, Loan, Point)>,

        cfg_node: BTreeSet<Point>,
        killed: Relation<(Loan, Point)>,

        cfg_edge: Relation<(Point, Point)>,
    }

    let mut block_facts: FxHashMap<usize, BlockContext> = Default::default();
    for block_idx in 0..block_count {
        let invalidates = block_invalidates.remove(&block_idx).unwrap_or_default();

        // TODO: filtrer les 3 relations suivantes pour ne traquer que les loans et origins intéressants
        let region_live_at: Vec<_> = block_region_live_at
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

        let ctx = BlockContext {
            region_live_at: region_live_at.into(),

            borrow_region,
            outlives,

            cfg_edge: cfg_edge.into(),
            cfg_node,
            killed: killed.into(),
            invalidates: invalidates.into(),
        };

        block_facts.insert(block_idx, ctx);
    }

    println!("block_count: {}", block_count);

    // TODO: maybe order the CFG better, eg a BFS here ?
    let mut blocks: VecDeque<_> = (0..block_count).collect();

    // println!("queue: {:?}", blocks.iter().take(10).collect::<Vec<_>>());

    let timer = Instant::now();

    let mut count = 0;
    while let Some(block_idx) = blocks.pop_front() {
        count += 1;

        if count > 100_000 {
            println!("nope, bailing out after too many iterations");
            break;
        }

        // println!("current block: {}", block_idx);
        // println!("block to visit: {} - queue: {:?}", block_idx, blocks.iter().take(5).collect::<Vec<_>>());
        // println!("block to visit: {} - queue: {:?}", block_idx, blocks.len());

        let bb_facts = &block_facts[&block_idx];

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

        let result = run_blocky(
            &known_contains,
            &placeholder_origin,
            &placeholder_loan,
            &bb_facts.region_live_at,
            &bb_facts.cfg_edge,
            &bb_facts.cfg_node,
            &bb_facts.killed,
            &bb_facts.invalidates,
            &bb_facts.borrow_region,
            &bb_facts.outlives,
        );
        // println!("new tuples: {:?}", result.new_tuples);
        // println!("errors: {:?}", result.errors.elements);

        // {
        //     println!();
        //     println!("bb {} - new tuples: {:?}", block_idx, result.new_tuples);
        //     println!("bb {} - input borrow_region: {:?}", block_idx, bb_facts.borrow_region.len());
        //     println!("bb {} - result requires: {:?}", block_idx, result.requires.len());
        //     println!("bb {} - input outlives: {:?}", block_idx, bb_facts.outlives.len());
        //     println!("bb {} - result subset: {:?}", block_idx, result.subset.len());

        //     if count == 2 {
        //         break;
        //     }
        // }

        if result.errors.len() > 0 {
            println!("\n");
            for error in result.errors.iter() {
                println!(
                    "found an error, {:?}, at {}",
                    error,
                    tables.points.untern(error.1)
                );
            }
            println!("\n");
        }

        if result.subset_errors.len() > 0 {
            println!("\n");
            for error in result.subset_errors.iter() {
                println!(
                    "found a subset error, {:?}, at {}",
                    error,
                    tables.points.untern(error.2)
                );
            }
            println!("\n");
        }

        // if we're not at a local fixpoint yet
        if result.new_tuples > 0 {
            if let Some(successor_blocks) = block_successor.get(&block_idx) {
                // println!("block {} to: {:?} - queue pre-merging: {:?}", block_idx, successor_blocks, blocks.iter().take(5).collect::<Vec<_>>());

                for &successor_block_idx in successor_blocks {
                    // println!("merging current block {}, with successor block {}", block_idx, successor_block_idx);
                    let successor_facts = block_facts.get_mut(&successor_block_idx).unwrap();

                    // merge requires / subsets at the block interface: the new block needs to know only the new facts
                    // at its entry point

                    // for fact in result.requires.iter() {
                    //     let (_point, local_block_idx) = block_from_point(fact.2);
                    //     if local_block_idx == successor_block_idx {
                    //         println!("merging 'requires' {:?} at {} from block {}, with block {}", fact, _point, block_idx, successor_block_idx);
                    //     }
                    // }

                    let successor_borrow_regions = successor_facts.borrow_region.len();
                    successor_facts
                        .borrow_region
                        .extend(result.requires.iter().filter(|fact| {
                            let (_, local_block_idx) = block_from_point(fact.2);
                            local_block_idx == successor_block_idx
                        }));

                    // for fact in result.subset.iter() {
                    //     let (_point, local_block_idx) = block_from_point(fact.2);
                    //     if local_block_idx == successor_block_idx {
                    //         println!("merging 'subset' {:?} at {} from block {}, with block {}", fact, _point, block_idx, successor_block_idx);
                    //     }
                    // }

                    let successor_outlives = successor_facts.outlives.len();
                    successor_facts
                        .outlives
                        .extend(result.subset.iter().filter(|fact| {
                            let (_, local_block_idx) = block_from_point(fact.2);
                            local_block_idx == successor_block_idx
                        }));

                    // we tried merging the result tuples in the successor blocks. if the tuple count didn't change, then re-running
                    // the computation on the successor would result in a result we already have. We're already at a fixpoint state for
                    // the successor block.

                    let is_successor_dirty = successor_facts.borrow_region.len()
                        != successor_borrow_regions
                        || successor_facts.outlives.len() != successor_outlives;

                    // println!("from block: {} - is successor {} dirty: {}", block_idx, successor_block_idx, is_successor_dirty);

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

    println!("\nblocky elapsed: {:?}, took {} iterations", timer.elapsed(), count);

    Ok(())
}

use crate::blocky::{BlockyResult, Context};
use crate::facts::LocalFacts;

fn create_function_data(
    all_facts: AllFacts,
) -> (
    Relation<(Origin, Loan)>,
    Relation<(Origin, ())>,
    Relation<(Loan, Origin)>,
    Vec<(Origin, Point)>,
) {
    use polonius_engine::output::initialization;
    use polonius_engine::output::liveness;
    use polonius_engine::output::{InitializationContext, LivenessContext};

    let mut result = Output::new(false);

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
    let known_contains = Output::compute_known_contains(&known_subset, &all_facts.placeholder);

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
    )
}

fn run_blocky(
    known_contains: &Relation<(Origin, Loan)>,
    placeholder_origin: &Relation<(Origin, ())>,
    placeholder_loan: &Relation<(Loan, Origin)>,
    block_region_live_at: &Relation<(Origin, Point)>,
    block_cfg_edge: &Relation<(Point, Point)>,
    block_cfg_node: &BTreeSet<Point>,
    block_killed: &Relation<(Loan, Point)>,
    block_invalidates: &Relation<(Loan, Point)>,
    block_borrow_region: &FxHashSet<(Origin, Loan, Point)>,
    block_outlives: &FxHashSet<(Origin, Origin, Point)>,
) -> BlockyResult<LocalFacts> {
    let mut result = Output::new(false);

    let ctx = Context::<LocalFacts> {
        region_live_at: block_region_live_at,
        invalidates: block_invalidates,
        cfg_edge: block_cfg_edge,
        cfg_node: block_cfg_node,
        outlives: block_outlives,
        borrow_region: block_borrow_region,
        killed: block_killed,
        known_contains: known_contains,
        placeholder_origin: placeholder_origin,
        placeholder_loan: placeholder_loan,
    };

    blocky::compute(&ctx, &mut result)
}
