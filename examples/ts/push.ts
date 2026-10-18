// The SDK's message source for an echod-server, which pushes.
//
// The SDK's default source long-polls the server; echod has no poll endpoint
// and POSTs each message to the worker's address instead. This adapter is that
// address: an HTTP listener whose URL is the worker's unicast and anycast, so
// every `resonate:target` and every listener registration names it. Plug it
// into the SDK's `HttpNetwork` and nothing else changes.

import http from "node:http";
import { type HttpAdapter, HttpNetwork, type Message, Resonate } from "@resonatehq/sdk";

export class PushMessageSource implements HttpAdapter {
  readonly unicast: string;
  readonly anycast: string;
  private server: http.Server;
  private callbacks: Array<(msg: Message) => void> = [];
  private groups: Record<string, string>;

  /// Listen on `port`; `groups` maps a group name a caller may use as a target
  /// to the URL of the worker that serves it.
  constructor({ port, host = "127.0.0.1", groups = {} }: { port: number; host?: string; groups?: Record<string, string> }) {
    this.unicast = `http://${host}:${port}/`;
    this.anycast = this.unicast;
    this.groups = groups;
    this.server = http.createServer((req, res) => {
      let body = "";
      req.on("data", (c) => {
        body += c;
      });
      req.on("end", () => {
        try {
          const msg = JSON.parse(body) as Message;
          for (const cb of this.callbacks) cb(msg);
          res.writeHead(200).end();
        } catch (e) {
          res.writeHead(400).end(String(e));
        }
      });
    });
  }

  match(target: string): string {
    return this.groups[target] ?? this.unicast;
  }

  init(): Promise<void> {
    const u = new URL(this.unicast);
    return new Promise((resolve) => this.server.listen(Number(u.port), u.hostname, () => resolve()));
  }

  stop(): Promise<void> {
    return new Promise((resolve) => this.server.close(() => resolve()));
  }

  onReceive(callback: (msg: Message) => void): void {
    this.callbacks.push(callback);
  }
}

export const SERVER = process.env.ECHOD_URL ?? "http://127.0.0.1:8001";

/// A Resonate instance that talks to echod and receives on `port`.
export function connect(port: number, groups: Record<string, string> = {}, opts: Record<string, unknown> = {}): Resonate {
  const adapter = new PushMessageSource({ port, groups });
  const network = new HttpNetwork({ url: SERVER, adapter });
  return new Resonate({ network, ...opts });
}
