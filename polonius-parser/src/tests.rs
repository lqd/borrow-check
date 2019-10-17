#![cfg(test)]

use crate::ir::{Effect, Fact, KnownSubset, PlaceholderOrigin};
use crate::parse_input;

#[test]
fn universal_regions() {
    let program = r"
        universal_regions { 'a, 'b, 'c }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap();
    assert_eq!(input.universal_regions, ["'a", "'b", "'c"]);
}

#[test]
fn blocks() {
    let program = r"
        universal_regions { 'a, 'b, 'c }
        block B0 {
        }
        block B1 {
        }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap();
    assert_eq!(
        input.blocks.iter().map(|b| &b.name).collect::<Vec<_>>(),
        ["B0", "B1"]
    );
}

#[test]
fn goto() {
    let program = r"
        universal_regions { 'a, 'b, 'c }
        block B0 {
            goto B1;
        }
        block B1 {
        }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap();
    assert_eq!(input.blocks[0].goto, ["B1"]);
}

#[test]
fn effects() {
    let program = r"
        universal_regions { 'a, 'b, 'c }
        block B0 {
            use('a), outlives('a: 'b), borrow_region_at('b, L1);
            kill(L2);
            invalidates(L0);
        }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap();
    let block = &input.blocks[0];
    assert_eq!(block.statements.len(), 3);

    let statements = &block.statements;
    assert_eq!(statements[0].effects.len(), 3);
    assert_eq!(statements[1].effects.len(), 1);
    assert_eq!(statements[2].effects.len(), 1);

    let effects = &statements[0].effects;
    assert_eq!(
        effects[0],
        Effect::Use {
            origins: vec!["'a".to_string()]
        }
    );
    assert_eq!(
        effects[1],
        Effect::Fact(Fact::Outlives {
            a: "'a".to_string(),
            b: "'b".to_string()
        })
    );
    assert_eq!(
        effects[2],
        Effect::Fact(Fact::BorrowRegionAt {
            origin: "'b".to_string(),
            loan: "L1".to_string()
        })
    );

    let effects = &statements[1].effects;
    assert_eq!(
        effects[0],
        Effect::Fact(Fact::Kill {
            loan: "L2".to_string()
        })
    );

    let effects = &statements[2].effects;
    assert_eq!(
        effects[0],
        Effect::Fact(Fact::Invalidates {
            loan: "L0".to_string()
        })
    );
}

#[test]
fn effects_start() {
    let program = r"
        universal_regions { 'a, 'b, 'c }
        block B0 {
            invalidates(L0), region_live_at('a) / use('a);
            invalidates(L1);
            invalidates(L0), invalidates(L1) / use('c);
        }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap();
    let block = &input.blocks[0];
    assert_eq!(block.statements.len(), 3);

    let statements = &block.statements[0];
    assert_eq!(
        statements.effects_start,
        [
            Effect::Fact(Fact::Invalidates {
                loan: "L0".to_string()
            }),
            Effect::Fact(Fact::RegionLiveAt {
                origin: "'a".to_string()
            })
        ]
    );
    assert_eq!(
        statements.effects,
        [Effect::Use {
            origins: vec!["'a".to_string()]
        }]
    );

    let statements = &block.statements[1];
    assert!(statements.effects_start.is_empty());
    assert_eq!(
        statements.effects,
        [Effect::Fact(Fact::Invalidates {
            loan: "L1".to_string()
        })]
    );

    let statements = &block.statements[2];
    assert_eq!(
        statements.effects_start,
        [
            Effect::Fact(Fact::Invalidates {
                loan: "L0".to_string()
            }),
            Effect::Fact(Fact::Invalidates {
                loan: "L1".to_string()
            })
        ]
    );
    assert_eq!(
        statements.effects,
        [Effect::Use {
            origins: vec!["'c".to_string()]
        }]
    );
}

#[test]
fn complete_example() {
    let program = r"
        // program description
        universal_regions { 'a, 'b, 'c }

        // block description
        block B0 {
            // 0:
            invalidates(L0);

            // 1:
            kill(L2);

            invalidates(L1) / use('a, 'b);

            // another comment
            goto B1, B2;
        }

        block B1 {
            use('a), outlives('a: 'b), borrow_region_at('b, L1);
        }
    ";
    assert!(parse_input(program).is_ok());
}

#[test]
fn variable_used() {
    let program = r"
        universal_regions { 'a, 'b, 'c }

        block B0 {
            var_used(V0);
        }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap();
    let block = &input.blocks[0];
    assert_eq!(block.statements.len(), 1);

    let statement = &block.statements[0];
    assert_eq!(
        statement.effects,
        [Effect::Fact(Fact::UseVariable {
            variable: "V0".to_string()
        })]
    );
}

#[test]
fn variable_defined() {
    let program = r"
        universal_regions { 'a, 'b, 'c }

        block B0 {
            var_defined(V1);
        }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap();
    let block = &input.blocks[0];
    assert_eq!(block.statements.len(), 1);

    let statement = &block.statements[0];
    assert_eq!(
        statement.effects,
        [Effect::Fact(Fact::DefineVariable {
            variable: "V1".to_string()
        })]
    );
}

#[test]
fn var_uses_region() {
    let program = r"
        universal_regions { 'a, 'b, 'c }
        var_uses_region { (V1, 'a), (V2, 'b) }
        var_drops_region {  }

        block B0 {
            var_defined(V1);
        }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap();
    assert_eq!(
        input.var_uses_region,
        [
            ("V1".to_string(), "'a".to_string()),
            ("V2".to_string(), "'b".to_string())
        ]
    );
}

#[test]
fn var_drops_region() {
    let program = r"
        universal_regions { 'a, 'b, 'c }
        var_uses_region {  }
        var_drops_region { (V1, 'a) }

        block B0 {
            var_defined(V1);
        }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap();
    assert_eq!(
        input.var_drops_region,
        [("V1".to_string(), "'a".to_string())]
    );
}

#[test]
fn known_subsets() {
    let program = r"
        universal_regions { 'a, 'b, 'c }
        known_subsets { 'a: 'b, 'b: 'c }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap();
    assert_eq!(input.universal_regions, ["'a", "'b", "'c"]);
    assert_eq!(
        input.known_subsets,
        vec![
            KnownSubset {
                a: "'a".to_string(),
                b: "'b".to_string()
            },
            KnownSubset {
                a: "'b".to_string(),
                b: "'c".to_string()
            }
        ]
    );
}

#[test]
fn placeholder_origins() {
    let program = r"
        universal_regions { 'a, 'b, 'c }
        placeholder_origins { 'a: L1, 'b: L2, 'c: L3 }
    ";
    let input = parse_input(program);
    assert!(input.is_ok());

    let input = input.unwrap(); 
    assert_eq!(input.universal_regions, ["'a", "'b", "'c"]);
    assert_eq!(
        input.placeholder_origins,
        vec![
            PlaceholderOrigin {
                origin: "'a".to_string(),
                loan: "L1".to_string()
            },
            PlaceholderOrigin {
                origin: "'b".to_string(),
                loan: "L2".to_string()
            },
            PlaceholderOrigin {
                origin: "'c".to_string(),
                loan: "L3".to_string()
            }
        ]
    );
}