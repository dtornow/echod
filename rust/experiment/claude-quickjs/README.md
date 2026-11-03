# Minimal Anthropic agent loop in QuickJS

This experiment runs a small agent loop directly against Anthropic's Messages
API inside QuickJS. It has no JavaScript dependencies and does not use an agent
SDK, API SDK, bundler, Claude Code, or child processes.

```shell
cargo run -p claude-quickjs -- "Say hello"
```

The command is expected to exit unsuccessfully at the first missing HTTP
capability. The agent loop executes inside QuickJS, but bare QuickJS does not
provide `fetch`.

`chat.mjs` contains the complete loop:

1. Send the conversation and an `add` tool definition to `/v1/messages`.
2. Append the assistant response.
3. Execute any requested tools in QuickJS and append their results.
4. Repeat until Claude returns no tool calls or the eight-turn limit is reached.

No Anthropic credentials are needed for the expected failure. If networking is
added later, the Rust host passes `ANTHROPIC_API_KEY` and the optional
`ANTHROPIC_MODEL` override into QuickJS.
