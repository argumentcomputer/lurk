use crate::lurk::cli::{
    config::{set_config, Config},
    repl::Repl,
};

#[test]
fn test_meta_commands() {
    set_config(Config::default());
    let mut repl = Repl::new();
    assert!(repl
        .load_file("src/lurk/cli/tests/first.lurk".into(), false)
        .is_ok());
    assert!(repl
        .load_file("src/lurk/cli/tests/second.lurk".into(), false)
        .is_ok());
    std::fs::remove_file("repl-test-two").unwrap();
}

#[ignore]
#[test]
fn test_meta_commands_with_proofs() {
    set_config(Config::default());
    let mut repl = Repl::new();
    assert!(repl
        .load_file("src/lurk/cli/tests/prove.lurk".into(), false)
        .is_ok());
    assert!(repl
        .load_file("src/lurk/cli/tests/verify.lurk".into(), false)
        .is_ok());
    std::fs::remove_file("repl-test-protocol-proof").unwrap();
    std::fs::remove_file("repl-test-protocol").unwrap();
}

#[test]
fn test_lib() {
    set_config(Config::default());
    let mut repl = Repl::new();
    assert!(repl.load_file("lib/tests.lurk".into(), false).is_ok());
}
