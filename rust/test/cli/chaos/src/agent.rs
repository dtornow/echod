//! chaos-agent: PID 1 of a node's container. It runs `echod` as its child
//! and, on a control port of its own, does to it what the world does to a
//! process: kills it, stops it, freezes it, cuts its network, slows it.
//!
//! ```text
//! chaos-agent --control 0.0.0.0:7000 -- echod --store s3://echod ...
//!
//! GET  /                                  running, pid, restarts, faults in force
//! POST /crash?after_ms=N                  SIGKILL; a fresh process after N ms
//! POST /stop?after_ms=N                   SIGTERM; a fresh process after N ms
//! POST /pause                             SIGSTOP: alive, answering nothing
//! POST /resume                            SIGCONT
//! POST /partition?hosts=a,b&port=P&dir=D  drop packets to and from those hosts
//!                                         (to port P only; dir in|out|both)
//! POST /netem?delay_ms=D&jitter_ms=J&loss=L   latency and loss on the device
//! POST /heal                              every rule and qdisc removed
//! ```
//!
//! The child is a real process on a real socket: a crash loses its cache and
//! its wheel, a pause outlives its announcement and it comes back believing
//! it is the owner, a partition from the store makes every write a timeout.
//! Nothing here touches the store; the store is where the truth is kept, and
//! the faults are everything around it.
//!
//! Needs `CAP_NET_ADMIN`, `iptables` and `tc` in the container.

use std::collections::HashMap;
use std::process::Stdio;
use std::sync::Arc;
use std::time::Duration;

use axum::extract::{Query, State};
use axum::http::StatusCode;
use axum::response::{IntoResponse, Json};
use axum::routing::{get, post};
use axum::Router;
use clap::Parser;
use serde::Serialize;
use tokio::process::{Child, Command};
use tokio::sync::Mutex;

#[derive(Debug, Parser)]
#[command(name = "chaos-agent", about = "Runs a process and does things to it", version)]
struct Args {
    /// Where the control port listens.
    #[arg(long, default_value = "0.0.0.0:7000")]
    control: String,
    /// The network device faults are applied to.
    #[arg(long, default_value = "eth0")]
    device: String,
    /// The command to run and keep running.
    #[arg(trailing_var_arg = true, required = true)]
    command: Vec<String>,
}

#[derive(Default, Serialize, Clone)]
struct Status {
    running: bool,
    paused: bool,
    pid: Option<u32>,
    starts: u64,
    kills: u64,
    stops: u64,
    partitions: Vec<String>,
    netem: Option<String>,
}

struct Agent {
    args: Args,
    child: Mutex<Option<Child>>,
    status: Mutex<Status>,
    /// How long the supervisor waits before starting the process again.
    pending_restart: Mutex<Option<Duration>>,
}

#[tokio::main]
async fn main() {
    let args = Args::parse();
    let agent = Arc::new(Agent { args, child: Mutex::new(None), status: Mutex::new(Status::default()), pending_restart: Mutex::new(None) });

    let app = Router::new()
        .route("/", get(status))
        .route("/crash", post(crash))
        .route("/stop", post(stop))
        .route("/pause", post(pause))
        .route("/resume", post(resume))
        .route("/partition", post(partition))
        .route("/netem", post(netem))
        .route("/heal", post(heal))
        .with_state(Arc::clone(&agent));
    let listener = tokio::net::TcpListener::bind(&agent.args.control).await.expect("control port");
    eprintln!("chaos-agent: control on http://{} for {:?}", agent.args.control, agent.args.command);
    tokio::spawn(async move { axum::serve(listener, app).await.expect("serve") });

    let supervisor = tokio::spawn(supervise(Arc::clone(&agent)));
    let mut term = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate()).expect("signal");
    tokio::select! {
        _ = term.recv() => {}
        _ = tokio::signal::ctrl_c() => {}
        _ = supervisor => {}
    }
    // The container is going: take the child with us, cleanly.
    if let Some(pid) = agent.status.lock().await.pid {
        signal(pid, libc::SIGCONT);
        signal(pid, libc::SIGTERM);
    }
    let child = agent.child.lock().await.take();
    if let Some(mut c) = child {
        let _ = tokio::time::timeout(Duration::from_secs(5), c.wait()).await;
    }
}

/// Start the process; when it dies, start it again after whatever delay a
/// fault asked for (none, if it died on its own).
async fn supervise(agent: Arc<Agent>) {
    loop {
        let mut cmd = Command::new(&agent.args.command[0]);
        cmd.args(&agent.args.command[1..]).stdin(Stdio::null()).kill_on_drop(false);
        let child = match cmd.spawn() {
            Ok(c) => c,
            Err(e) => {
                eprintln!("chaos-agent: cannot start {:?}: {e}", agent.args.command);
                tokio::time::sleep(Duration::from_secs(1)).await;
                continue;
            }
        };
        let pid = child.id();
        {
            let mut s = agent.status.lock().await;
            s.running = true;
            s.paused = false;
            s.pid = pid;
            s.starts += 1;
        }
        eprintln!("chaos-agent: started pid {pid:?}");
        *agent.child.lock().await = Some(child);
        // Wait without holding the lock, so a fault can reach the child.
        let exit = loop {
            let mut guard = agent.child.lock().await;
            match guard.as_mut() {
                Some(c) => match c.try_wait() {
                    Ok(Some(status)) => break Some(status),
                    Ok(None) => {}
                    Err(_) => break None,
                },
                None => break None,
            }
            drop(guard);
            tokio::time::sleep(Duration::from_millis(50)).await;
        };
        eprintln!("chaos-agent: pid {pid:?} exited: {exit:?}");
        *agent.child.lock().await = None;
        let delay = agent.pending_restart.lock().await.take().unwrap_or(Duration::ZERO);
        {
            let mut s = agent.status.lock().await;
            s.running = false;
            s.paused = false;
            s.pid = None;
        }
        tokio::time::sleep(delay).await;
    }
}

fn signal(pid: u32, sig: libc::c_int) -> bool {
    // SAFETY: a plain kill(2) on a pid we started.
    unsafe { libc::kill(pid as libc::pid_t, sig) == 0 }
}

fn after(q: &HashMap<String, String>) -> Duration {
    Duration::from_millis(q.get("after_ms").and_then(|v| v.parse().ok()).unwrap_or(0))
}

async fn status(State(a): State<Arc<Agent>>) -> Json<Status> {
    Json(a.status.lock().await.clone())
}

async fn crash(State(a): State<Arc<Agent>>, Query(q): Query<HashMap<String, String>>) -> impl IntoResponse {
    terminate(&a, libc::SIGKILL, after(&q)).await;
    a.status.lock().await.kills += 1;
    StatusCode::OK
}

async fn stop(State(a): State<Arc<Agent>>, Query(q): Query<HashMap<String, String>>) -> impl IntoResponse {
    terminate(&a, libc::SIGTERM, after(&q)).await;
    a.status.lock().await.stops += 1;
    StatusCode::OK
}

async fn terminate(a: &Agent, sig: libc::c_int, delay: Duration) {
    *a.pending_restart.lock().await = Some(delay);
    if let Some(pid) = a.status.lock().await.pid {
        // A stopped process does not take a SIGTERM until it runs again.
        signal(pid, libc::SIGCONT);
        signal(pid, sig);
        eprintln!("chaos-agent: sent {sig} to {pid}; back after {delay:?}");
    }
}

async fn pause(State(a): State<Arc<Agent>>) -> impl IntoResponse {
    let mut s = a.status.lock().await;
    match s.pid {
        Some(pid) if signal(pid, libc::SIGSTOP) => {
            s.paused = true;
            eprintln!("chaos-agent: paused {pid}");
            StatusCode::OK
        }
        _ => StatusCode::CONFLICT,
    }
}

async fn resume(State(a): State<Arc<Agent>>) -> impl IntoResponse {
    let mut s = a.status.lock().await;
    if let Some(pid) = s.pid {
        signal(pid, libc::SIGCONT);
        eprintln!("chaos-agent: resumed {pid}");
    }
    s.paused = false;
    StatusCode::OK
}

async fn sh(program: &str, args: &[&str]) -> Result<(), String> {
    let out = Command::new(program).args(args).output().await.map_err(|e| format!("{program}: {e}"))?;
    if out.status.success() {
        Ok(())
    } else {
        Err(format!("{program} {}: {}", args.join(" "), String::from_utf8_lossy(&out.stderr).trim()))
    }
}

/// Drop every packet to and from `hosts` (resolved now), to `port` only if
/// given, in `dir` (`in`, `out`, `both`).
async fn partition(State(a): State<Arc<Agent>>, Query(q): Query<HashMap<String, String>>) -> impl IntoResponse {
    let hosts: Vec<&str> = q.get("hosts").map(|h| h.split(',').filter(|h| !h.is_empty()).collect()).unwrap_or_default();
    if hosts.is_empty() {
        return (StatusCode::BAD_REQUEST, "hosts=a,b".to_string());
    }
    let port = q.get("port").cloned();
    let dir = q.get("dir").map(String::as_str).unwrap_or("both");
    let mut applied = Vec::new();
    for host in hosts {
        let addrs = match tokio::net::lookup_host((host, 1)).await {
            Ok(it) => it.map(|a| a.ip().to_string()).collect::<Vec<_>>(),
            Err(e) => return (StatusCode::BAD_REQUEST, format!("{host}: {e}")),
        };
        for ip in addrs {
            let mut rules: Vec<Vec<String>> = Vec::new();
            if dir != "out" {
                let mut r = vec!["-I".into(), "INPUT".into(), "-s".into(), ip.clone()];
                if let Some(p) = &port {
                    r.extend(["-p".into(), "tcp".into(), "--dport".into(), p.clone()]);
                }
                r.extend(["-j".into(), "DROP".into()]);
                rules.push(r);
            }
            if dir != "in" {
                let mut r = vec!["-I".into(), "OUTPUT".into(), "-d".into(), ip.clone()];
                if let Some(p) = &port {
                    r.extend(["-p".into(), "tcp".into(), "--dport".into(), p.clone()]);
                }
                r.extend(["-j".into(), "DROP".into()]);
                rules.push(r);
            }
            for r in rules {
                let args: Vec<&str> = r.iter().map(String::as_str).collect();
                if let Err(e) = sh("iptables", &args).await {
                    return (StatusCode::INTERNAL_SERVER_ERROR, e);
                }
            }
            applied.push(format!("{host}={ip}{} {dir}", port.as_ref().map(|p| format!(":{p}")).unwrap_or_default()));
        }
    }
    // Whatever is cut, the control port stays open, or the fault could not
    // be lifted: first in each chain, above every drop.
    if let Some(cp) = a.args.control.rsplit(':').next() {
        for (chain, side) in [("INPUT", "--dport"), ("OUTPUT", "--sport")] {
            if let Err(e) = sh("iptables", &["-I", chain, "1", "-p", "tcp", side, cp, "-j", "ACCEPT"]).await {
                return (StatusCode::INTERNAL_SERVER_ERROR, e);
            }
        }
    }
    eprintln!("chaos-agent: partitioned from {applied:?}");
    a.status.lock().await.partitions.extend(applied);
    (StatusCode::OK, String::new())
}

async fn netem(State(a): State<Arc<Agent>>, Query(q): Query<HashMap<String, String>>) -> impl IntoResponse {
    let delay = q.get("delay_ms").cloned().unwrap_or_else(|| "0".into());
    let jitter = q.get("jitter_ms").cloned().unwrap_or_else(|| "0".into());
    let loss = q.get("loss").cloned().unwrap_or_else(|| "0".into());
    let spec = format!("delay {delay}ms {jitter}ms loss {loss}%");
    let args = ["qdisc", "replace", "dev", &a.args.device, "root", "netem", "delay", &format!("{delay}ms"), &format!("{jitter}ms"), "loss", &format!("{loss}%")];
    match sh("tc", &args).await {
        Ok(()) => {
            eprintln!("chaos-agent: netem {spec}");
            a.status.lock().await.netem = Some(spec);
            (StatusCode::OK, String::new())
        }
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, e),
    }
}

async fn heal(State(a): State<Arc<Agent>>) -> impl IntoResponse {
    let _ = sh("iptables", &["-F", "INPUT"]).await;
    let _ = sh("iptables", &["-F", "OUTPUT"]).await;
    let _ = sh("tc", &["qdisc", "del", "dev", &a.args.device, "root"]).await;
    let mut s = a.status.lock().await;
    if let Some(pid) = s.pid {
        signal(pid, libc::SIGCONT);
    }
    s.paused = false;
    s.partitions.clear();
    s.netem = None;
    eprintln!("chaos-agent: healed");
    StatusCode::OK
}
