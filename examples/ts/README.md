# echod examples, TypeScript

The Resonate TypeScript SDK against `echod`. The SDK's default message
source long-polls; echod pushes, so `push.ts` is the worker's side of HTTP
push: an HTTP listener plugged into the SDK's `HttpNetwork` as its adapter.

```shell
cargo run --release -p echod                 # in-memory store, :8001
until curl -sf localhost:8001/ready; do sleep 1; done   # ready once it has read a configuration naming it
cd examples/ts && npm install
npm run hello
npm run fibonacci -- --mode mix --n 8
npm run sleep
npm run human -- --decision reject
npm run rpc
npm run retries
```

`ECHOD_URL` points the examples at another server.
