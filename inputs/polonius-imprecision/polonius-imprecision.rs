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
        x.0 = &z; // creates {L0} in 'x constraint
        // at this point, we have `'x: 'y` and `{L0} in `'x`, so we also have `{L0} in 'y`
        drop(x.0);
    }

    z += 1; // polonius flags an (unnecessary) error

    drop(y.0);
}

fn main() {}