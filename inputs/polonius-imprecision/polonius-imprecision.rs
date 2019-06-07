#![feature(nll)]
#![allow(warnings)]

fn unnecessary_error() {
    let mut x: (&u32,) = (&0,);
    let mut y: (&u32,) = (&1,);
    let mut z = 2;

    if false {
        y.0 = x.0; // creates `'x: 'y` subset relation
    }

    if false {
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

fn g() -> i32 {
    0
}

fn main() {}
