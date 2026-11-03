# Claude Agent SDK in QuickJS

This experiment mounts the JavaScript entry point from Anthropic's Claude Agent
SDK in an otherwise bare QuickJS runtime and attempts one chat turn.

```shell
cd rust/experiment/claude-quickjs
npm ci
cd ../../..
cargo run -p claude-quickjs -- "Say hello"
```

The command is expected to exit unsuccessfully. The first boundary is earlier
than a network request: the SDK's standard entry point requires Node.js and
imports `node:module`. Its `query()` implementation later spawns the bundled
Claude Code CLI as a child process. Bare QuickJS supplies neither Node built-ins,
process spawning, nor networking.

The crate intentionally mounts only the SDK module. Its resolver rejects the
first host capability the SDK asks for and reports that import, giving the next
experiment a precise starting point.

The npm lockfile pins the package used by the experiment. No Anthropic
credentials are needed because execution stops while linking the module.
