// retries: a flaky leaf is retried until it succeeds; the workflow around it
// is replayed, never retried.
import { Constant, type Context } from "@resonatehq/sdk";
import { connect } from "./push.js";

const POLICY = new Constant({ delay: 0, maxRetries: 5 });

class Gateway {
  private attempts = new Map<string, number>();
  charge(key: string, amount: number): string {
    const n = (this.attempts.get(key) ?? 0) + 1;
    this.attempts.set(key, n);
    console.log(`  [${key}] attempt ${n}`);
    if (n <= 2) throw new Error(`timeout (attempt ${n})`);
    return `charged $${amount}`;
  }
}

async function charge(ctx: Context, key: string, amount: number): Promise<string> {
  return ctx.getDependency<Gateway>("gateway")!.charge(key, amount);
}

function* checkout(ctx: Context): Generator<any, string, any> {
  const viaRun: string = yield* ctx.run(charge, "ctx.run", 300, ctx.options({ retryPolicy: POLICY }));
  const viaRpc: string = yield* ctx.rpc<string>("charge", "ctx.rpc", 400, ctx.options({ retryPolicy: POLICY }));
  return `${viaRun} | ${viaRpc}`;
}

const resonate = connect(9107);
resonate.setDependency("gateway", new Gateway());
resonate.register("checkout", checkout);
resonate.register("charge", charge);

const ts = Date.now();
try {
  const a = await resonate.run(`retries-run-${ts}`, charge, "resonate.run", 100, resonate.options({ retryPolicy: POLICY }));
  console.log(`resonate.run -> ${a}`);
  const b = await resonate.rpc(`retries-rpc-${ts}`, "charge", "resonate.rpc", 200, resonate.options({ retryPolicy: POLICY }));
  console.log(`resonate.rpc -> ${b}`);
  const c = await resonate.run(`retries-checkout-${ts}`, checkout);
  console.log(`checkout -> ${c}`);
} finally {
  await resonate.stop();
}
