use crate::lurk::cli::{
    config::{set_config_if_unset, Config},
    repl::Repl,
};

#[test]
fn test_meta_commands() {
    set_config_if_unset(Config::default());
    let mut repl = Repl::new_native();
    assert!(repl
        .load_file("src/lurk/cli/tests/first.lurk".into(), false)
        .is_ok());
    let mut repl = Repl::new_native();
    assert!(repl
        .load_file("src/lurk/cli/tests/second.lurk".into(), false)
        .is_ok());
    std::fs::remove_file("repl-test-two").unwrap();
}

#[ignore]
#[test]
fn test_meta_commands_with_proofs() {
    set_config_if_unset(Config::default());
    let mut repl = Repl::new_native();
    assert!(repl
        .load_file("src/lurk/cli/tests/prove.lurk".into(), false)
        .is_ok());
    let mut repl = Repl::new_native();
    assert!(repl
        .load_file("src/lurk/cli/tests/verify.lurk".into(), false)
        .is_ok());
    std::fs::remove_file("repl-test-protocol-proof").unwrap();
    std::fs::remove_file("repl-test-protocol").unwrap();
}

#[test]
fn test_lib() {
    set_config_if_unset(Config::default());
    let mut repl = Repl::new_native();
    assert!(repl.load_file("lib/tests.lurk".into(), false).is_ok());
}

#[ignore]
#[test]
fn test_demo_files() {
    set_config_if_unset(Config::default());
    let demo_files = [
        "demo/simple.lurk",
        "demo/functional-commitment.lurk",
        "demo/chained-functional-commitment.lurk",
        "demo/protocol.lurk",
        "demo/bank.lurk",
        "demo/mastermind.lurk",
        "demo/mini-mastermind.lurk",
        "demo/microbank.lurk",
    ];
    for file in demo_files {
        let mut repl = Repl::new_native();
        assert!(repl.load_file(file.into(), false).is_ok());
    }
    std::fs::remove_file("protocol-proof").unwrap();
}
