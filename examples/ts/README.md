# echod examples, TypeScript

The Resonate TypeScript SDK against `echod-server`. The SDK's default message
source long-polls; echod pushes, so `push.ts` is the worker's side of HTTP
push: an HTTP listener plugged into the SDK's `HttpNetwork` as its adapter.

```shell
cargo run --release -p echod-server          # in-memory store, :8001
cd examples/ts && npm install
npm run hello
npm run fibonacci -- --mode mix --n 8
npm run sleep
npm run human -- --decision reject
npm run rpc
npm run retries
```

`ECHOD_URL` points the examples at another server.
