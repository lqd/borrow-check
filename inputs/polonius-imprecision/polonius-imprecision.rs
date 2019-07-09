#![feature(nll)]
#![allow(warnings)]

fn unnecessary_error() {
    let mut x: (&u32,) = (&0,);
    let mut y: (&u32,) = (&1,);
    let mut z = 2;

    if random_bool() {
        y.0 = x.0; // creates `'x: 'y` subset relation
    }

    if random_bool() {
        x.0 = &z; // creates `{L0} in 'x` constraint
        // at this point, we have `'x: 'y` and `{L0} in 'x`, so we also have `{L0} in 'y`
        drop(x.0);
    }

    z += 1; // polonius flags an (unnecessary) error

    drop(y.0);
}

fn cycle_unification() {
    let mut x = 0;
    let mut v: Vec<&u32> = vec![]; // `'v`

    let p: &mut Vec<&u32> = &mut v; // `'p`, which could be unified with `'v`
    let q = &x; // creates `{L0}`

    p.push(q); // adds `{L0}` to `'p`, needs to *indirectly* add to `'v`.
    // If unified, this would add `{L0}` to `'v`
    
    x += 1; // error. Unified: an error because `{L0} in 'v` and `v` is live
    drop(v);
}

fn cfg_propagation_required(x: &mut &i32) {
    let y = x;
    *y = &g();
}

fn flow_sensitive_equality_required() {
    let mut a: Vec<&u32> = vec![];
    let mut b: Vec<&u32> = vec![];
    let mut c: Vec<&u32> = vec![];
    let mut p: &mut Vec<&u32> = &mut c;
    let mut i = 22;
    if random_bool() {
        p = &mut a;
        p.push(&i);
        drop(a);
        i += 1; // `i` is no longer borrowed, ok
        drop(b);
    } else {
        p = &mut b;
        p.push(&i);
        drop(b);
        i += 1; // `i` is no longer borrowed, ok
        drop(a);
    }
}

struct Thing;

impl Thing {
    fn next(&mut self) -> &mut Self { unimplemented!() }
}

// a mix between rand's loop and 47680
fn loopdydoo() {
    let mut temp = &mut Thing;

    loop {
        let v = temp.next();
        temp = v; // accepted by NLL, incorrectly rejected by Polonius
    }
}

// ui/span/regions-escape-loop-via-vec.rs
// The type of `y` ends up getting inferred to the type of the block.
fn broken() {
    let mut x = 3;
    let mut _y = vec![&mut x];
    while x < 10 { //~ ERROR cannot use `x` because it was mutably borrowed
        let mut z = x; //~ ERROR cannot use `x` because it was mutably borrowed
        _y.push(&mut z);
        //~^ ERROR `z` does not live long enough
        x += 1; //~ ERROR cannot use `x` because it was mutably borrowed
    }
}

//

fn random_bool() -> bool {
    true
}

fn g() -> i32 {
    0
}

fn main() {}
