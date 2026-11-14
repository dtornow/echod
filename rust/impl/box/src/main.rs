use std::env;
use std::ffi::{OsStr, OsString};
use std::io::{self, IsTerminal};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use clap::Parser;

const WORKSPACE: &str = "/workspace";
const GLOBAL_CONFIG: &str = "/box/.box.nix";

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

    /// Copy a named host environment variable into the box.
    #[arg(long, env = "BOX_CREDENTIALS", value_delimiter = ',', value_parser = credential_name)]
    credential: Vec<String>,

    /// Command to run instead of opening an interactive terminal.
    #[arg(last = true)]
    command: Vec<String>,
}

fn credential_name(value: &str) -> Result<String, String> {
    let mut chars = value.chars();
    if !matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        || !chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Err("expected an environment variable name, not a value or assignment".into());
    }
    Ok(value.to_owned())
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
    if let Some(name) = cli
        .credential
        .iter()
        .find(|name| env::var_os(name).is_none())
    {
        eprintln!("box: credential {name} is not set in the host environment");
        return ExitCode::FAILURE;
    }

    let terminal = io::stdin().is_terminal() && io::stdout().is_terminal();
    let global_config = global_config_dir();
    let args = docker_args(
        &directory,
        global_config.as_deref(),
        &cli.image,
        &cli.credential,
        &cli.command,
        terminal,
    );
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
    global_config: Option<&Path>,
    image: &OsStr,
    credentials: &[String],
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
        volume_mount(directory, WORKSPACE, false),
    ]);
    if let Some(config) = global_config {
        args.extend(["--volume".into(), volume_mount(config, "/box", true)]);
    }
    for credential in credentials {
        args.extend(["--env".into(), credential.into()]);
    }
    args.extend([
        "--entrypoint".into(),
        "/bin/sh".into(),
        image.into(),
        "-c".into(),
        startup_script(
            global_config.is_some(),
            directory.join("box.nix").is_file(),
            command,
        )
        .into(),
    ]);
    args
}

fn global_config_dir() -> Option<PathBuf> {
    let directory = PathBuf::from(env::var_os("HOME")?).join(".box");
    directory.join(".box.nix").is_file().then_some(directory)
}

fn volume_mount(source: &Path, target: &str, read_only: bool) -> OsString {
    let mut mount = source.as_os_str().to_owned();
    mount.push(format!(":{target}"));
    if read_only {
        mount.push(":ro");
    }
    mount
}

fn startup_script(global: bool, project: bool, args: &[String]) -> String {
    let mut command = if args.is_empty() {
        "exec bash -i".into()
    } else {
        format!("exec {}", shell_join(args))
    };
    let mut configs = Vec::new();
    if global {
        configs.push(GLOBAL_CONFIG);
    }
    if project {
        configs.push("/workspace/box.nix");
    }
    for config in configs.into_iter().rev() {
        command = format!("exec nix-shell {config} --run {}", shell_quote(&command));
    }
    command
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
    fn credentials_accept_names_not_assignments() {
        assert_eq!(
            credential_name("ANTHROPIC_API_KEY").unwrap(),
            "ANTHROPIC_API_KEY"
        );
        for invalid in ["", "KEY=value", "1KEY", "--env", "A B"] {
            assert!(credential_name(invalid).is_err());
        }
    }

    #[test]
    fn nonterminal_container_has_no_tty_or_credentials_by_default() {
        let args = docker_args(
            Path::new("/tmp/project"),
            None,
            OsStr::new("nixos/nix:test"),
            &[],
            &["true".into()],
            false,
        );
        for absent in ["--tty", "--interactive", "--env"] {
            assert!(!args.contains(&OsString::from(absent)));
        }
    }

    #[test]
    fn quotes_shell_arguments_without_interpolation() {
        assert_eq!(shell_quote("hello world"), "'hello world'");
        assert_eq!(shell_quote("it's $HOME"), "'it'\"'\"'s $HOME'");
        assert_eq!(shell_quote(""), "''");
    }

    #[test]
    fn applies_global_then_project_config_before_shell() {
        let script = startup_script(true, true, &[]);
        let project = format!(
            "exec nix-shell /workspace/box.nix --run {}",
            shell_quote("exec bash -i")
        );
        assert_eq!(
            script,
            format!(
                "exec nix-shell /box/.box.nix --run {}",
                shell_quote(&project)
            )
        );
    }

    #[test]
    fn runs_commands_inside_or_outside_nix_shell() {
        let args = ["printf".into(), "%s\n".into(), "hello; echo unsafe".into()];
        let script = startup_script(false, true, &args);
        let run = "'printf' '%s\n' 'hello; echo unsafe'";
        assert_eq!(
            script,
            format!(
                "exec nix-shell /workspace/box.nix --run {}",
                shell_quote(&format!("exec {run}"))
            )
        );
        assert_eq!(startup_script(false, false, &args), format!("exec {run}"));
    }

    #[test]
    fn creates_an_ephemeral_attached_container() {
        let args = docker_args(
            Path::new("/tmp/my project"),
            Some(Path::new("/home/me/.box")),
            OsStr::new("nixos/nix:test"),
            &["ANTHROPIC_API_KEY".into()],
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
        assert!(strings.contains(&"/tmp/my project:/workspace".into()));
        assert!(strings.contains(&"/home/me/.box:/box:ro".into()));
        assert!(strings
            .windows(2)
            .any(|pair| pair == ["--env", "ANTHROPIC_API_KEY"]));
        assert!(strings
            .windows(2)
            .any(|pair| pair == ["/bin/sh", "nixos/nix:test"]));
    }
}
