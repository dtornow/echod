# Lean side of the Lean-vs-Rust benchmark

`bench.lean` runs the `length` and `fanout` workloads of
`resonatehq/resonate-specification` `valid/lean/experiments.lean` on that
repository's trace checker, one workload and size per process, so peak memory
is per case. `resonate/examples/resonate_bench.rs` runs the same workloads on the Rust
checker.

To use it, copy it into a checkout of resonate-specification and add to its
`lakefile.lean`:

```lean
lean_exe «bench» where
  srcDir := "."
  root   := `«valid».«lean».bench
```

then:

```
cp bench.lean <resonate-specification>/valid/lean/bench.lean
lake build bench
.lake/build/bin/bench length 2 4 6 7
.lake/build/bin/bench fanout 8 64 256 512 1024
.lake/build/bin/bench fanout-nocone 8 10 11 12
```

Built against resonate-specification `6b120ad` with Lean 4.31.0.
