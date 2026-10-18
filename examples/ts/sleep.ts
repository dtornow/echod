// sleep: a countdown whose sleeps are timer promises the server fires. The
// worker suspends between ticks; echod's timer keys wake it.
import type { Context } from "@resonatehq/sdk";
import { connect } from "./push.js";

function* countdown(ctx: Context, count: number, delayMs: number): Generator<any, string, any> {
  for (let i = count; i > 0; i--) {
    yield* ctx.run((_ctx: Context) => console.log(`  countdown: ${i}`));
    yield* ctx.sleep(delayMs);
  }
  return "done";
}

const resonate = connect(9103);
resonate.register("countdown", countdown);

const t0 = Date.now();
const out = await resonate.run(`countdown-${t0}`, countdown, 3, 1000);
console.log(`${out} after ${Date.now() - t0} ms`);

await resonate.stop();
