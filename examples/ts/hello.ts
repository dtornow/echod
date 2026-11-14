// hello: register, invoke durably, print. ctx.run keeps bar local; ctx.rpc
// dispatches baz through the server, which pushes it back to this worker.
import type { Context } from "@resonatehq/sdk";
import { connect } from "./push.js";

function* foo(ctx: Context, name: string): Generator<any, string, any> {
  return yield* ctx.run(bar, name);
}

function* bar(ctx: Context, name: string): Generator<any, string, any> {
  return yield* ctx.rpc<string>("baz", name);
}

async function baz(_ctx: Context, name: string): Promise<string> {
  return `hello, ${name}!`;
}

const resonate = connect(9101);
resonate.register("foo", foo);
resonate.register("baz", baz);

const id = `hello-${Date.now()}`;
console.log(await resonate.run(id, foo, "world"));

await resonate.stop();
