globalThis.fetch = async function fetch(url, options = {}) {
  const wire = JSON.parse(
    globalThis.__host_fetch(
      String(url),
      String(options.method ?? "GET"),
      String(options.body ?? ""),
    ),
  );

  if (wire.transport_error !== undefined) {
    throw new TypeError(wire.transport_error);
  }

  return {
    ok: wire.ok,
    status: wire.status,
    text: async () => wire.body,
    json: async () => JSON.parse(wire.body),
  };
};
