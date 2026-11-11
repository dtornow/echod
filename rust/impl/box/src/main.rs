use std::env;
use std::ffi::{OsStr, OsString};
use std::io::{self, IsTerminal};
use std::path::Path;
use std::process::{Command, ExitCode};

use clap::Parser;

const WORKSPACE: &str = "/workspace";

/// Start an ephemeral development box in the current directory.
#[derive(Debug, Parser)]
#[command(version, about)]
struct Cli {
    /// OCI runtime to invoke.
    #[arg(long, env = "BOX_RUNTIME", default_value = "docker")]
    runtime: OsString,

    /// Container image containing Nix and Bash.
    #[arg(long, env = "BOX_IMAGE", default_value = "nixos/nix:latest")]
    image: OsString,

    /// Command to run instead of opening an interactive terminal.
    #[arg(last = true)]
    command: Vec<String>,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let directory = match env::current_dir().and_then(|path| path.canonicalize()) {
        Ok(directory) => directory,
        Err(error) => {
            eprintln!("box: could not resolve the current directory: {error}");
            return ExitCode::FAILURE;
        }
    };

    let terminal = io::stdin().is_terminal() && io::stdout().is_terminal();
    let args = docker_args(&directory, &cli.image, &cli.command, terminal);
    match Command::new(&cli.runtime).args(args).status() {
        Ok(status) if status.success() => ExitCode::SUCCESS,
        Ok(status) => ExitCode::from(status.code().unwrap_or(1).clamp(1, 255) as u8),
        Err(error) => {
            eprintln!(
                "box: could not start {}: {error}",
                cli.runtime.to_string_lossy()
            );
            ExitCode::from(127)
        }
    }
}

fn docker_args(
    directory: &Path,
    image: &OsStr,
    command: &[String],
    terminal: bool,
) -> Vec<OsString> {
    let mut args = vec!["run".into(), "--rm".into(), "--init".into()];
    if terminal {
        args.push("--interactive".into());
        args.push("--tty".into());
    }
    args.extend([
        "--workdir".into(),
        WORKSPACE.into(),
        "--volume".into(),
        volume_mount(directory),
        "--entrypoint".into(),
        "/bin/sh".into(),
        image.into(),
        "-c".into(),
        startup_script(command).into(),
    ]);
    args
}

fn volume_mount(directory: &Path) -> OsString {
    let mut mount = directory.as_os_str().to_owned();
    mount.push(format!(":{WORKSPACE}"));
    mount
}

fn startup_script(command: &[String]) -> String {
    if command.is_empty() {
        return format!(
            "if [ -f {WORKSPACE}/box.nix ]; then\n\
             \texec nix-shell {WORKSPACE}/box.nix\n\
             else\n\
             \texec bash -l\n\
             fi"
        );
    }

    let command = shell_join(command);
    let nix_command = shell_quote(&format!("exec {command}"));
    format!(
        "if [ -f {WORKSPACE}/box.nix ]; then\n\
         \texec nix-shell {WORKSPACE}/box.nix --run {nix_command}\n\
         else\n\
         \texec {command}\n\
         fi"
    )
}

fn shell_join(args: &[String]) -> String {
    args.iter()
        .map(|arg| shell_quote(arg))
        .collect::<Vec<_>>()
        .join(" ")
}

fn shell_quote(value: &str) -> String {
    if value.is_empty() {
        return "''".into();
    }
    format!("'{}'", value.replace('\'', "'\"'\"'"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quotes_shell_arguments_without_interpolation() {
        assert_eq!(shell_quote("hello world"), "'hello world'");
        assert_eq!(shell_quote("it's $HOME"), "'it'\"'\"'s $HOME'");
        assert_eq!(shell_quote(""), "''");
    }

    #[test]
    fn opens_nix_shell_when_box_file_exists() {
        let script = startup_script(&[]);
        assert!(script.contains("if [ -f /workspace/box.nix ]"));
        assert!(script.contains("exec nix-shell /workspace/box.nix"));
        assert!(script.contains("exec bash -l"));
    }

    #[test]
    fn runs_commands_inside_or_outside_nix_shell() {
        let script = startup_script(&["printf".into(), "%s\n".into(), "hello; echo unsafe".into()]);
        let run = "'printf' '%s\n' 'hello; echo unsafe'";
        assert!(script.contains(&format!(
            "exec nix-shell /workspace/box.nix --run {}",
            shell_quote(&format!("exec {run}"))
        )));
        assert!(script.contains("exec 'printf' '%s\n' 'hello; echo unsafe'"));
    }

    #[test]
    fn creates_an_ephemeral_attached_container() {
        let args = docker_args(
            Path::new("/tmp/my project"),
            OsStr::new("nixos/nix:test"),
            &[],
            true,
        );
        let strings = args
            .iter()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect::<Vec<_>>();

        assert_eq!(
            &strings[..6],
            [
                "run",
                "--rm",
                "--init",
                "--interactive",
                "--tty",
                "--workdir"
            ]
        );
        assert!(strings
            .windows(2)
            .any(|pair| pair == ["/tmp/my project:/workspace", "--entrypoint"]));
        assert!(strings
            .windows(2)
            .any(|pair| pair == ["/bin/sh", "nixos/nix:test"]));
    }
}
