// human-in-the-loop: the workflow suspends on a promise an outsider resolves.
// --decision approve | reject
import { Codec, type Context } from "@resonatehq/sdk";
import { connect } from "./push.js";

interface Decision {
  approve: boolean;
  note: string;
}

class ReviewerInbox {
  private resolve!: (id: string) => void;
  readonly approvalId = new Promise<string>((r) => {
    this.resolve = r;
  });
  private done = false;
  publish(id: string): void {
    if (!this.done) {
      this.done = true;
      this.resolve(id);
    }
  }
}

async function notifyReviewer(ctx: Context, orderId: string, amount: number, approvalId: string): Promise<string> {
  console.log(`  [notifyReviewer] order ${orderId} ($${amount}) needs approval; promise ${approvalId}`);
  ctx.getDependency<ReviewerInbox>("inbox")!.publish(approvalId);
  return approvalId;
}

async function shipOrder(_ctx: Context, orderId: string, note: string): Promise<string> {
  console.log(`  [shipOrder] shipping ${orderId} (${note})`);
  return `shipped-${orderId}`;
}

async function cancelOrder(_ctx: Context, orderId: string, note: string): Promise<string> {
  console.log(`  [cancelOrder] canceling ${orderId} (${note})`);
  return `canceled-${orderId}`;
}

function* fulfillOrder(ctx: Context, orderId: string, amount: number): Generator<any, string, any> {
  const approval = yield* ctx.promise<Decision>();
  yield* ctx.run(notifyReviewer, orderId, amount, approval.id);
  const decision: Decision = yield* approval;
  if (decision.approve) return yield* ctx.run(shipOrder, orderId, decision.note);
  return yield* ctx.run(cancelOrder, orderId, decision.note);
}

function flag(name: string, fallback: string): string {
  const i = process.argv.indexOf(`--${name}`);
  return i >= 0 && process.argv[i + 1] ? process.argv[i + 1] : fallback;
}

const approve = flag("decision", "approve") === "approve";

const resonate = connect(9104);
const inbox = new ReviewerInbox();
resonate.setDependency("inbox", inbox);
resonate.register("fulfillOrder", fulfillOrder);
const codec = new Codec();

async function simulateReviewer(decision: Decision): Promise<void> {
  const approvalId = await inbox.approvalId;
  await new Promise((r) => setTimeout(r, 500));
  await resonate.promises.resolve(approvalId, { data: codec.encode(decision).data });
  console.log(`  [reviewer] resolved ${approvalId} -> approve=${decision.approve}`);
}

try {
  const wid = `fulfill-${Date.now()}`;
  const decision: Decision = { approve, note: approve ? "looks good" : "policy violation" };
  const reviewer = simulateReviewer(decision);
  const out = await resonate.run(wid, fulfillOrder, "order-42", 199);
  await reviewer;
  const expected = approve ? "shipped-order-42" : "canceled-order-42";
  if (out !== expected) throw new Error(`expected ${expected}, got ${out}`);
  console.log(`fulfillOrder: ${out}`);
} finally {
  await resonate.stop();
}
