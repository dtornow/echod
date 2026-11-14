# Minimal Anthropic agent loop in QuickJS

This experiment runs a small agent loop directly against Anthropic's Messages
API inside QuickJS. It has no JavaScript dependencies and does not use an agent
SDK, API SDK, bundler, Claude Code, or child processes.

```shell
# Supply ANTHROPIC_API_KEY securely in your environment first.
cargo run -p claude-quickjs -- --model <model-available-to-your-account> "Say hello"
```

Rust installs a synchronous, minimal `fetch` shim before starting the loop. The
shim supports only the Response fields used here: `ok`, `status`, `text()`, and
`json()`. Its host broker permits only `POST
https://api.anthropic.com/v1/messages`, rejects redirects, limits request and
response sizes, and applies a two-minute timeout. Rust adds the API key and
required headers, so the credential is never exposed inside QuickJS.

`chat.mjs` contains the complete loop:

1. Send the conversation and an `add` tool definition to `/v1/messages`.
2. Append the assistant response.
3. Execute any requested tools in QuickJS and append their results.
4. Repeat until Claude returns no tool calls or the eight-turn limit is reached.

An explicit prompt and model are required; `ANTHROPIC_MODEL` can supply the
model instead of `--model`. There is no default model or automatic request
when invoked without arguments. Running this command makes paid API calls
(up to eight turns). `--help` and `cargo test -p claude-quickjs --locked`
do not need credentials or make API requests: the loop test uses synthetic
responses, not a live provider. Live account/model availability is not tested.

This is a standalone experiment, not an SDK or a server dependency. Building
QuickJS requires a native C compiler. The host reads `chat.mjs` next to this
manifest at runtime, so retain the source checkout when running the binary.
The synchronous request blocks the QuickJS runtime; that is intentional for
this first implementation.
