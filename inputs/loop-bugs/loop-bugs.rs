#![feature(nll)]

// Except the _fixed cases, all these are rejected by Polonius and accepted by NLL

// invalidating, killing at the same mir statement ?
fn loop1() {
    let mut buf = &mut 0;
    loop {
        buf = index_mut(buf); // accepted by NLL, rejected by Polonius
    }
}

// loop1 with a temporary to make invalidating + killing on two different points ?
fn loop1_fixed() {
    let mut buf = &mut 0;
    loop {
        let tmp = index_mut(buf); // 2) ... but polonius itself still flags an error here
        buf = tmp; // 1) now accepted by rustc -Z polonius...
    }
}

use std::{io, mem};
use std::io::Read;

fn rand_loop(r: &mut dyn Read, mut buf: &mut [u8]) -> io::Result<()> {
    while buf.len() > 0 {
        match r.read(buf).unwrap() {
            0 => return Err(io::Error::new(io::ErrorKind::Other,
                                           "end of file reached")),
            n => buf = &mut mem::replace(&mut buf, &mut [])[n..], // accepted by NLL, rejected by Polonius
        }
    }
    Ok(())
}

fn rand_loop_tiny(mut buf: &mut [u8]) {
    loop {
        buf = &mut buf[..];
    }
}

// reducing this lead to loop1
fn rand_loop_tiny_no_parameters() {
    let mut orig = [0];
    let mut buf: &mut [u8] = &mut orig;
    loop {
        buf = &mut buf[..]; // accepted by NLL, rejected by Polonius
    }
}

// test: region escape via vec, NLL has 1 error, Polonius 2 (and seems to work with in house Vec and push)
fn broken_minimized() {
    let mut x = Vec::new();
    loop {
        let mut y = 0; // Polonius rejects this as an assignment to borrowed value
        x.push(&mut y); // error: y doesn't live long enough
    }
}

fn index_mut(_a: &mut u32) -> &mut u32 {
    panic!();
}

fn main() {}