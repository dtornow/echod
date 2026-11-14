const API_URL = "https://api.anthropic.com/v1/messages";
const MAX_TURNS = 8;

const tools = [
  {
    name: "add",
    description: "Add two numbers.",
    input_schema: {
      type: "object",
      properties: {
        left: { type: "number" },
        right: { type: "number" },
      },
      required: ["left", "right"],
      additionalProperties: false,
    },
  },
];

async function createMessage(messages) {
  const response = await fetch(API_URL, {
    method: "POST",
    body: JSON.stringify({
      model: globalThis.__anthropic_model,
      max_tokens: 1024,
      messages,
      tools,
    }),
  });

  if (!response.ok) {
    throw new Error(`Anthropic API ${response.status}: ${await response.text()}`);
  }

  return response.json();
}

async function executeTool(toolUse) {
  if (toolUse.name !== "add") {
    throw new Error(`Unknown tool: ${toolUse.name}`);
  }

  const { left, right } = toolUse.input;
  if (typeof left !== "number" || typeof right !== "number") {
    throw new Error("The add tool requires numeric left and right arguments.");
  }

  return String(left + right);
}

async function runAgent(prompt) {
  const messages = [{ role: "user", content: prompt }];

  for (let turn = 0; turn < MAX_TURNS; turn += 1) {
    const response = await createMessage(messages);
    messages.push({ role: "assistant", content: response.content });

    const toolUses = response.content.filter((block) => block.type === "tool_use");
    if (toolUses.length === 0) {
      return { response, turns: turn + 1 };
    }

    const toolResults = [];
    for (const toolUse of toolUses) {
      try {
        toolResults.push({
          type: "tool_result",
          tool_use_id: toolUse.id,
          content: await executeTool(toolUse),
        });
      } catch (error) {
        toolResults.push({
          type: "tool_result",
          tool_use_id: toolUse.id,
          content: String(error),
          is_error: true,
        });
      }
    }
    messages.push({ role: "user", content: toolResults });
  }

  throw new Error(`Agent exceeded ${MAX_TURNS} turns.`);
}

globalThis.__claude_result = JSON.stringify(
  await runAgent(globalThis.__claude_prompt),
);
