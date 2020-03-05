#![crate_type = "lib"]
#![feature(nll)]
#![allow(unused_assignments)]
#![allow(unused_variables)]

fn missing_subset<'a, 'b>(a: &'a u32, b: &'b u32) -> &'a u32 {
    b //~ ERROR lifetime may not live long enough
}

fn missing_transitive_subsets<'a, 'b, 'c>(a: &'a u32, mut b: &'b u32, mut c: &'c u32) {
    b = a; //~ lifetime may not live long enough
    c = b; //~ lifetime may not live long enough
    //^ lifetime may not live long enough
}

fn implied_bounds_subset<'a, 'b>(x: &'a &'b mut u32) -> &'a u32 {
    x
}

fn valid_subset<'a, 'b: 'a>(a: &'a u32, b: &'b u32) -> &'a u32 {
    b
}

// As `'a: 'c` holds transitively, it will not be emitted in the `known_subset` relation,
// Polonius needs to compute its transitive closure to not miss the relationship is present.
fn valid_transitive_subsets<'a: 'b, 'b: 'c, 'c>(a: &'a u32, mut b: &'b u32, mut c: &'c u32) {
    b = a;
    c = b;
}
