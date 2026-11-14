# Strands Box vendoring

The `credentials` and `egress-gateway` crates in this directory are copied
without modification from
[`strands-agents/box`](https://github.com/strands-agents/box) at revision
`8a5f9ba262a5260b269b25ac6a75bf74abcdc89c`.

They are licensed under Apache-2.0. See `LICENSE`, `NOTICE`, and
`THIRD-PARTY-NOTICES` in this directory. The optional `strands-proxy` Cargo
feature compiles these sources; the default build does not use them.
