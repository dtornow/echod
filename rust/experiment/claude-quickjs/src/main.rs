use std::{env, fs, path::PathBuf, process::ExitCode};

use rquickjs::{CatchResultExt, Context, Module, Runtime};

const ENTRY_MODULE: &str = "claude-quickjs-chat.mjs";

fn script_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("chat.mjs")
}

fn run(prompt: &str) -> Result<(), String> {
    let path = script_path();
    let script =
        fs::read(&path).map_err(|error| format!("could not read {}: {error}", path.display()))?;

    let runtime = Runtime::new().map_err(|error| error.to_string())?;
    let context = Context::full(&runtime).map_err(|error| error.to_string())?;

    context.with(|ctx| {
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
        ctx.globals()
            .set(
                "__anthropic_model",
                env::var("ANTHROPIC_MODEL").unwrap_or_else(|_| "claude-sonnet-5-5".to_owned()),
            )
            .catch(&ctx)
            .map_err(|error| error.to_string())?;

        let evaluation = Module::evaluate(ctx.clone(), ENTRY_MODULE, script)
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

    println!("QuickJS: loading a manual Anthropic Messages API loop");
    println!("QuickJS: starting chat with prompt: {prompt:?}");

    match run(&prompt) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("QuickJS stopped before a chat could start:\n{error}");
            eprintln!(
                "\nExpected boundary: the complete agent loop runs in QuickJS, but bare QuickJS \
                 has no `fetch` implementation for its first Messages API request."
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

    #[test]
    fn agent_executes_a_tool_and_returns_the_second_response() {
        let runtime = Runtime::new().unwrap();
        let context = Context::full(&runtime).unwrap();

        context.with(|ctx| {
            ctx.globals().set("__claude_prompt", "Add 2 and 3").unwrap();
            ctx.globals()
                .set("__anthropic_api_key", "test-key")
                .unwrap();
            ctx.globals()
                .set("__anthropic_model", "test-model")
                .unwrap();
            ctx.eval::<(), _>(
                r#"
                    globalThis.__requests = [];
                    globalThis.fetch = async (_url, options) => {
                        const request = JSON.parse(options.body);
                        globalThis.__requests.push(request);
                        if (globalThis.__requests.length === 1) {
                            return {
                                ok: true,
                                json: async () => ({
                                    stop_reason: "tool_use",
                                    content: [{
                                        type: "tool_use",
                                        id: "tool-1",
                                        name: "add",
                                        input: { left: 2, right: 3 }
                                    }]
                                })
                            };
                        }
                        return {
                            ok: true,
                            json: async () => ({
                                stop_reason: "end_turn",
                                content: [{ type: "text", text: "The answer is 5." }]
                            })
                        };
                    };
                "#,
            )
            .unwrap();

            Module::evaluate(ctx.clone(), "test-agent.mjs", include_bytes!("../chat.mjs"))
                .unwrap()
                .finish::<()>()
                .unwrap();

            let result: String = ctx.eval("globalThis.__claude_result").unwrap();
            let requests: String = ctx.eval("JSON.stringify(globalThis.__requests)").unwrap();
            assert!(result.contains(r#""turns":2"#));
            assert!(result.contains("The answer is 5."));
            assert!(requests.contains(r#""type":"tool_result""#));
            assert!(requests.contains(r#""content":"5""#));
        });
    }
}
