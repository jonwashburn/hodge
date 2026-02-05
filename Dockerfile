# Dockerfile for Hodge Conjecture autonomous agent containers
# Based on Anthropic's agent teams methodology
#
# Build:  docker build -t hodge-agent .
# Run:    docker run -v /path/to/bare-repo:/upstream hodge-agent
#
# For multi-agent:
#   for i in $(seq 1 N); do
#     docker run -d --name hodge-agent-$i -v /path/to/bare-repo:/upstream hodge-agent
#   done

FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

# System dependencies
RUN apt-get update && apt-get install -y \
    curl git wget ca-certificates build-essential \
    python3 nodejs npm \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | \
    bash -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# Install Claude Code CLI
RUN npm install -g @anthropic-ai/claude-code

# Set up workspace
WORKDIR /workspace

# Entry point: clone from upstream, run agent loop
COPY scripts/docker_entrypoint.sh /docker_entrypoint.sh
RUN chmod +x /docker_entrypoint.sh

ENTRYPOINT ["/docker_entrypoint.sh"]
