// rpc: two workers on one server. The frontend has nothing registered and
// dispatches to the backend by target; the server pushes the task there.
import type { Context } from "@resonatehq/sdk";
import { connect } from "./push.js";

async function greet(_ctx: Context, name: string): Promise<string> {
  console.log(`  backend: greeting ${name}`);
  return `hello from backend, ${name}!`;
}

const backend = connect(9105);
backend.register("greet", greet);

// The frontend knows the backend by name.
const frontend = connect(9106, { backend: "http://127.0.0.1:9105/" });

try {
  const result = await frontend.rpc(`rpc-${Date.now()}`, "greet", "world", frontend.options({ target: "backend" }));
  if (result !== "hello from backend, world!") throw new Error(`unexpected: ${result}`);
  console.log(`frontend: got ${JSON.stringify(result)}`);
} finally {
  await frontend.stop();
  await backend.stop();
}
