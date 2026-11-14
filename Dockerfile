# syntax=docker/dockerfile:1
# One image with everything a deployment and its tests are made of: `echod`,
# `fakes3` (the S3 surface echod uses, in memory), `chaos-agent` (runs a
# process and does things to it) and `echod-chaos` (the clients and the
# check). `compose.yaml` runs them as a fleet; `scripts/chaos.sh` runs the
# fleet under faults.
FROM rust:1-bookworm AS build
WORKDIR /src
COPY . .
RUN --mount=type=cache,target=/usr/local/cargo/registry \
    --mount=type=cache,target=/usr/local/cargo/git \
    --mount=type=cache,target=/src/target \
    cargo build --release --locked -p echod -p fakes3 -p echod-chaos \
    && mkdir -p /out \
    && cp target/release/echod target/release/fakes3 target/release/chaos-agent target/release/echod-chaos /out/

FROM debian:bookworm-slim
# iptables and tc: what chaos-agent cuts and slows the network with.
RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates iptables iproute2 \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /out/ /usr/local/bin/
ENTRYPOINT ["echod"]
