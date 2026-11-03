import Anthropic from "@anthropic-ai/sdk";

const client = new Anthropic({
  apiKey: globalThis.__anthropic_api_key,
  dangerouslyAllowBrowser: true,
});

const finalMessage = await client.beta.messages.toolRunner({
  model: "claude-sonnet-5-5",
  max_tokens: 1024,
  messages: [{ role: "user", content: globalThis.__claude_prompt }],
  tools: [],
});

globalThis.__claude_result = JSON.stringify(finalMessage);
