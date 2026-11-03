# In-process Anthropic agent loop in QuickJS

This experiment bundles Anthropic's TypeScript API SDK into an otherwise bare
QuickJS runtime and attempts one chat turn through the SDK's in-process tool
runner. It does not use the Claude Agent SDK, Claude Code, or child processes.

```shell
cd rust/experiment/claude-quickjs
npm ci
npm run bundle
cd ../../..
cargo run -p claude-quickjs -- "Say hello"
```

The command is expected to exit unsuccessfully at the first missing HTTP
capability. The SDK and agent loop execute inside QuickJS, but bare QuickJS does
not provide `fetch`.

`esbuild` produces one browser-targeted module so QuickJS does not need Node's
module resolver. The generated `dist/` directory is intentionally untracked.

The npm lockfile pins the SDK and bundler. No Anthropic credentials are needed
for the expected failure. If networking is added later, the runner reads
`ANTHROPIC_API_KEY` from the Rust host.
