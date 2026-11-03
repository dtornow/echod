use std::{env, fs, path::PathBuf, process::ExitCode};

use rquickjs::{CatchResultExt, Context, Module, Runtime};

const SDK_MODULE: &str = "@anthropic-ai/sdk";
const ENTRY_MODULE: &str = "claude-quickjs-chat.mjs";

fn bundle_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("dist")
        .join("chat.mjs")
}

fn run(prompt: &str) -> Result<(), String> {
    let path = bundle_path();
    let bundle = fs::read(&path).map_err(|error| {
        format!(
            "could not read {}: {error}\n\
             Install and bundle the pinned in-process SDK with:\n\
             (cd {} && npm ci && npm run bundle)",
            path.display(),
            env!("CARGO_MANIFEST_DIR")
        )
    })?;

    let runtime = Runtime::new().map_err(|error| error.to_string())?;
    let context = Context::full(&runtime).map_err(|error| error.to_string())?;

    context.with(|ctx| {
        ctx.eval::<(), _>(
            "globalThis.console = { debug() {}, info() {}, log() {}, warn() {}, error() {} };",
        )
        .catch(&ctx)
        .map_err(|error| error.to_string())?;
        ctx.globals()
            .set("__claude_prompt", prompt)
            .catch(&ctx)
            .map_err(|error| error.to_string())?;
        ctx.globals()
            .set(
                "__anthropic_api_key",
                env::var("ANTHROPIC_API_KEY").unwrap_or_else(|_| "sandbox-probe".to_owned()),
            )
            .catch(&ctx)
            .map_err(|error| error.to_string())?;

        let evaluation = Module::evaluate(ctx.clone(), ENTRY_MODULE, bundle)
            .catch(&ctx)
            .map_err(|error| error.to_string())?;
        evaluation
            .finish::<()>()
            .catch(&ctx)
            .map_err(|error| error.to_string())?;

        let result: String = ctx
            .eval("globalThis.__claude_result")
            .catch(&ctx)
            .map_err(|error| error.to_string())?;
        println!("{result}");
        Ok(())
    })
}

fn main() -> ExitCode {
    let prompt = env::args()
        .nth(1)
        .unwrap_or_else(|| "Reply with exactly: hello from Claude".to_owned());

    println!("QuickJS: loading {SDK_MODULE}");
    println!("QuickJS: starting one-turn chat with prompt: {prompt:?}");

    match run(&prompt) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("QuickJS stopped before a chat could start:\n{error}");
            eprintln!(
                "\nExpected boundary: the API SDK and its tool runner execute in this QuickJS \
                 process, but bare QuickJS has no HTTP host capability."
            );
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bare_quickjs_has_no_fetch_capability() {
        let runtime = Runtime::new().unwrap();
        let context = Context::full(&runtime).unwrap();

        context.with(|ctx| {
            let fetch_type: String = ctx.eval("typeof globalThis.fetch").unwrap();
            assert_eq!(fetch_type, "undefined");
        });
    }
}
