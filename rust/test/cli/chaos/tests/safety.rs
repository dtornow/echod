use std::process::Command;

#[test]
fn agent_refuses_to_inject_faults_outside_a_disposable_container() {
    for args in [
        vec!["--", "/bin/true"],
        vec!["--owned-test-node", "--", "/bin/true"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_chaos-agent"))
            .args(args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(String::from_utf8_lossy(&output.stderr).contains("must be PID 1"));
    }
}

#[test]
fn empty_workload_is_not_a_successful_run() {
    let output = Command::new(env!("CARGO_BIN_EXE_echod-chaos"))
        .args(["--clients", "0"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("must be nonempty"));
}
