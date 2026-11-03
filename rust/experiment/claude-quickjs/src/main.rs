use std::{env, fs, path::PathBuf, process::ExitCode};

use rquickjs::{
    loader::{ImportAttributes, Loader, Resolver},
    module::Declared,
    CatchResultExt, Context, Ctx, Error, Module, Result as JsResult, Runtime,
};

const SDK_MODULE: &str = "@anthropic-ai/claude-agent-sdk";
const ENTRY_MODULE: &str = "claude-quickjs-chat.mjs";

struct AgentSdkResolver;

impl Resolver for AgentSdkResolver {
    fn resolve<'js>(
        &mut self,
        _ctx: &Ctx<'js>,
        base: &str,
        name: &str,
        _attributes: Option<ImportAttributes<'js>>,
    ) -> JsResult<String> {
        if name == SDK_MODULE {
            return Ok(name.to_owned());
        }

        Err(Error::new_resolving_message(
            base,
            name,
            format!(
                "QuickJS host capability missing: `{name}`. \
                 Only `{SDK_MODULE}` is mounted in this sandbox."
            ),
        ))
    }
}

struct AgentSdkLoader {
    source: Vec<u8>,
}

impl Loader for AgentSdkLoader {
    fn load<'js>(
        &mut self,
        ctx: &Ctx<'js>,
        name: &str,
        _attributes: Option<ImportAttributes<'js>>,
    ) -> JsResult<Module<'js, Declared>> {
        if name != SDK_MODULE {
            return Err(Error::new_loading(name));
        }

        Module::declare(ctx.clone(), name, self.source.clone())
    }
}

fn sdk_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("node_modules")
        .join("@anthropic-ai")
        .join("claude-agent-sdk")
        .join("sdk.mjs")
}

fn run(prompt: &str) -> Result<(), String> {
    let path = sdk_path();
    let sdk_source = fs::read(&path).map_err(|error| {
        format!(
            "could not read {}: {error}\n\
             Install the pinned JavaScript package with:\n\
             (cd {} && npm ci)",
            path.display(),
            env!("CARGO_MANIFEST_DIR")
        )
    })?;

    let runtime = Runtime::new().map_err(|error| error.to_string())?;
    runtime.set_loader(AgentSdkResolver, AgentSdkLoader { source: sdk_source });
    let context = Context::full(&runtime).map_err(|error| error.to_string())?;

    context.with(|ctx| {
        ctx.globals()
            .set("__claude_prompt", prompt)
            .catch(&ctx)
            .map_err(|error| error.to_string())?;

        let source = format!(
            r#"
                import {{ query }} from "{SDK_MODULE}";

                globalThis.__claude_messages = [];
                for await (const message of query({{
                    prompt: globalThis.__claude_prompt,
                    options: {{ maxTurns: 1 }}
                }})) {{
                    globalThis.__claude_messages.push(JSON.stringify(message));
                }}
            "#
        );

        let evaluation = Module::evaluate(ctx.clone(), ENTRY_MODULE, source)
            .catch(&ctx)
            .map_err(|error| error.to_string())?;
        evaluation
            .finish::<()>()
            .catch(&ctx)
            .map_err(|error| error.to_string())?;

        let messages: String = ctx
            .eval("JSON.stringify(globalThis.__claude_messages)")
            .catch(&ctx)
            .map_err(|error| error.to_string())?;
        println!("{messages}");
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
                "\nExpected boundary: the Agent SDK's Node entry point imports Node built-ins \
                 and later spawns the Claude Code CLI. Bare QuickJS provides neither capability, \
                 so this happens before any network request."
            );
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolver_mounts_only_the_agent_sdk() {
        let runtime = Runtime::new().unwrap();
        let context = Context::full(&runtime).unwrap();
        let mut resolver = AgentSdkResolver;

        context.with(|ctx| {
            assert_eq!(
                resolver
                    .resolve(&ctx, ENTRY_MODULE, SDK_MODULE, None)
                    .unwrap(),
                SDK_MODULE
            );
            assert!(resolver
                .resolve(&ctx, SDK_MODULE, "node:module", None)
                .unwrap_err()
                .is_resolving());
        });
    }
}
