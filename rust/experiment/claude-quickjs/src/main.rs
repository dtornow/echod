use std::{env, fs, io::Read, path::PathBuf, process::ExitCode, time::Duration};

use reqwest::{blocking::Client, redirect::Policy};
use rquickjs::{CatchResultExt, Context, Function, Module, Runtime};
use serde_json::json;

const ENTRY_MODULE: &str = "claude-quickjs-chat.mjs";
const ANTHROPIC_MESSAGES_URL: &str = "https://api.anthropic.com/v1/messages";
const MAX_REQUEST_BYTES: usize = 1024 * 1024;
const MAX_RESPONSE_BYTES: usize = 10 * 1024 * 1024;

struct FetchBroker {
    api_key: String,
    client: Client,
}

impl FetchBroker {
    fn new(api_key: String) -> Result<Self, String> {
        let client = Client::builder()
            .https_only(true)
            .redirect(Policy::none())
            .timeout(Duration::from_secs(120))
            .build()
            .map_err(|error| format!("could not create HTTP client: {error}"))?;
        Ok(Self { api_key, client })
    }

    fn fetch(&self, url: &str, method: &str, body: &str) -> String {
        self.try_fetch(url, method, body)
            .unwrap_or_else(|error| json!({ "transport_error": error }).to_string())
    }

    fn try_fetch(&self, url: &str, method: &str, body: &str) -> Result<String, String> {
        if url != ANTHROPIC_MESSAGES_URL {
            return Err(format!("fetch blocked URL: {url}"));
        }
        if !method.eq_ignore_ascii_case("POST") {
            return Err(format!("fetch blocked method: {method}"));
        }
        if body.len() > MAX_REQUEST_BYTES {
            return Err(format!("fetch request exceeded {MAX_REQUEST_BYTES} bytes"));
        }
        serde_json::from_str::<serde_json::Value>(body)
            .map_err(|error| format!("fetch request body is not valid JSON: {error}"))?;

        let response = self
            .client
            .post(ANTHROPIC_MESSAGES_URL)
            .header("content-type", "application/json")
            .header("x-api-key", &self.api_key)
            .header("anthropic-version", "2026-10-21")
            .body(body.to_owned())
            .send()
            .map_err(|error| format!("Anthropic request failed: {error}"))?;
        let status = response.status();
        let mut bytes = Vec::new();
        response
            .take((MAX_RESPONSE_BYTES + 1) as u64)
            .read_to_end(&mut bytes)
            .map_err(|error| format!("could not read Anthropic response: {error}"))?;
        if bytes.len() > MAX_RESPONSE_BYTES {
            return Err(format!(
                "fetch response exceeded {MAX_RESPONSE_BYTES} bytes"
            ));
        }
        let body = String::from_utf8(bytes)
            .map_err(|error| format!("Anthropic response was not UTF-8: {error}"))?;

        Ok(json!({
            "ok": status.is_success(),
            "status": status.as_u16(),
            "body": body,
        })
        .to_string())
    }
}

fn script_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("chat.mjs")
}

fn run(prompt: &str) -> Result<(), String> {
    let path = script_path();
    let script =
        fs::read(&path).map_err(|error| format!("could not read {}: {error}", path.display()))?;
    let api_key = env::var("ANTHROPIC_API_KEY")
        .map_err(|_| "ANTHROPIC_API_KEY is required to call the Messages API".to_owned())?;
    let broker = FetchBroker::new(api_key)?;

    let runtime = Runtime::new().map_err(|error| error.to_string())?;
    let context = Context::full(&runtime).map_err(|error| error.to_string())?;

    context.with(move |ctx| {
        let host_fetch = Function::new(
            ctx.clone(),
            move |url: String, method: String, body: String| broker.fetch(&url, &method, &body),
        )
        .catch(&ctx)
        .map_err(|error| error.to_string())?;
        ctx.globals()
            .set("__host_fetch", host_fetch)
            .catch(&ctx)
            .map_err(|error| error.to_string())?;
        ctx.eval::<(), _>(include_str!("../fetch-shim.js"))
            .catch(&ctx)
            .map_err(|error| error.to_string())?;
        ctx.globals()
            .set("__claude_prompt", prompt)
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
                "\nThe synchronous fetch shim permits only POST requests to \
                 {ANTHROPIC_MESSAGES_URL}; Rust owns the API key, timeout, and size limits."
            );
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, rc::Rc};

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
    fn fetch_broker_rejects_other_urls_and_methods_without_networking() {
        let broker = FetchBroker::new("test-key".to_owned()).unwrap();

        let wrong_url: serde_json::Value =
            serde_json::from_str(&broker.fetch("https://example.com/", "POST", "{}")).unwrap();
        let wrong_method: serde_json::Value =
            serde_json::from_str(&broker.fetch(ANTHROPIC_MESSAGES_URL, "GET", "{}")).unwrap();

        assert_eq!(
            wrong_url["transport_error"],
            "fetch blocked URL: https://example.com/"
        );
        assert_eq!(wrong_method["transport_error"], "fetch blocked method: GET");
    }

    #[test]
    fn agent_executes_a_tool_and_returns_the_second_response() {
        let runtime = Runtime::new().unwrap();
        let context = Context::full(&runtime).unwrap();
        let requests = Rc::new(RefCell::new(Vec::new()));
        let recorded_requests = Rc::clone(&requests);

        context.with(|ctx| {
            ctx.globals().set("__claude_prompt", "Add 2 and 3").unwrap();
            ctx.globals()
                .set("__anthropic_model", "test-model")
                .unwrap();
            let host_fetch = Function::new(
                ctx.clone(),
                move |url: String, method: String, body: String| {
                    recorded_requests.borrow_mut().push((url, method, body));
                    let content = if recorded_requests.borrow().len() == 1 {
                        json!([{
                            "type": "tool_use",
                            "id": "tool-1",
                            "name": "add",
                            "input": { "left": 2, "right": 3 }
                        }])
                    } else {
                        json!([{ "type": "text", "text": "The answer is 5." }])
                    };
                    json!({
                        "ok": true,
                        "status": 200,
                        "body": json!({ "content": content }).to_string(),
                    })
                    .to_string()
                },
            )
            .unwrap();
            ctx.globals().set("__host_fetch", host_fetch).unwrap();
            ctx.eval::<(), _>(include_str!("../fetch-shim.js")).unwrap();

            Module::evaluate(ctx.clone(), "test-agent.mjs", include_bytes!("../chat.mjs"))
                .unwrap()
                .finish::<()>()
                .unwrap();

            let result: String = ctx.eval("globalThis.__claude_result").unwrap();
            assert!(result.contains(r#""turns":2"#));
            assert!(result.contains("The answer is 5."));
        });

        let requests = requests.borrow();
        assert_eq!(requests.len(), 2);
        assert!(requests
            .iter()
            .all(|(url, method, _)| url == ANTHROPIC_MESSAGES_URL && method == "POST"));
        assert!(requests[1].2.contains(r#""type":"tool_result""#));
        assert!(requests[1].2.contains(r#""content":"5""#));
    }
}
