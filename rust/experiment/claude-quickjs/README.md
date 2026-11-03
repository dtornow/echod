# Minimal Anthropic agent loop in QuickJS

This experiment runs a small agent loop directly against Anthropic's Messages
API inside QuickJS. It has no JavaScript dependencies and does not use an agent
SDK, API SDK, bundler, Claude Code, or child processes.

```shell
export ANTHROPIC_API_KEY=...
cargo run -p claude-quickjs -- "Say hello"
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

`ANTHROPIC_MODEL` optionally overrides the default `claude-sonnet-5-5` model.
The synchronous request blocks the QuickJS runtime; that is intentional for
this first implementation.
