mod dump;
mod facts;
mod intern;
mod program;
mod tab_delim;
mod test;
mod test_util;

pub mod cli;

use std::error::Error;
use std::path::Path;

pub fn blocky() -> Result<(), Box<dyn Error>> {
    // let facts_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
    //     .join("inputs")
    //     .join("smoke-test")
    //     .join("nll-facts")
    //     .join("well_formed_function_inputs");

    // let facts_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
    //     .join("inputs")
    //     .join("subset-relations")
    //     .join("nll-facts")
    //     .join("missing_subset");

    // let facts_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
    //     .join("inputs")
    //     .join("vec-push-ref")
    //     .join("nll-facts")
    //     .join("foo1");

    let facts_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("inputs")
        .join("clap-rs")
        .join("app-parser-{{impl}}-add_defaults");

    // TODO: check that facts are not lost at the interface between 2 blocks
    // for this example there's an edge from mid bb7.7 to bb9, verify that eg the
    // requires facts are 1) computed at the edge, 2) transported along this edge,
    // so that the computation is correct in bb9
    // bb9 is weird anyway here, maybe an unwind/false/imaginary edge
    // -> check this for other blocks as well, but eg bb13 to 14 is correct

    let mut tables = intern::InternerTables::new();
    let facts = tab_delim::load_tab_delimited_facts(&mut tables, &facts_dir)?;
    let mut result = polonius_engine::Output::new(false);
    polonius_engine::output::blocky::blockify_my_love(facts, &tables, &mut result);
    Ok(())
}
