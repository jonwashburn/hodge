# Deploying Autonomous Agent Teams for the Hodge Proof

This guide walks you through deploying multiple Claude agents that work 24/7
on eliminating sorries from the Hodge Conjecture formalization.

## Prerequisites

1. **Claude API key** (Anthropic) with access to `claude-opus-4-6`
2. **Docker** installed on a Linux machine (or Mac with Docker Desktop)
3. **Git** configured with push access to this repo
4. **~$50-200/day budget** depending on agent count (estimate: ~$10-20/agent/day)

## Quick Start (Single Agent, No Docker)

The simplest setup — one agent in a terminal:

```bash
# 1. Export your API key
export ANTHROPIC_API_KEY="sk-ant-..."

# 2. Install Claude Code CLI
npm install -g @anthropic-ai/claude-code

# 3. Clone the repo
git clone <repo-url> hodge && cd hodge
git checkout claude/hodge-conjecture-proof-VSeH8

# 4. Set up Lean
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y
source ~/.profile
lake exe cache get
lake build  # verify everything works

# 5. Run the agent loop
./scripts/agent_loop.sh
```

The agent will run indefinitely, picking up tasks, committing progress, and looping.

## Multi-Agent Setup (Recommended: Docker)

This runs N agents in parallel, each in its own container, pushing to a shared branch.

### Step 1: Create a bare upstream repo

```bash
# On your host machine
mkdir -p ~/hodge-upstream
cd ~/hodge-upstream
git init --bare

# Push current state to it
cd /path/to/hodge
git remote add upstream ~/hodge-upstream
git push upstream claude/hodge-conjecture-proof-VSeH8
```

### Step 2: Build the Docker image

```bash
cd /path/to/hodge
docker build -t hodge-agent .
```

### Step 3: Launch agents

```bash
# Set your API key
export ANTHROPIC_API_KEY="sk-ant-..."

# Launch N agents (e.g., 4)
for i in $(seq 1 4); do
    docker run -d \
        --name hodge-agent-$i \
        -e ANTHROPIC_API_KEY=$ANTHROPIC_API_KEY \
        -e BRANCH=claude/hodge-conjecture-proof-VSeH8 \
        -e MODEL=claude-opus-4-6 \
        -v ~/hodge-upstream:/upstream \
        hodge-agent
    echo "Launched agent $i"
    sleep 5  # stagger starts
done
```

### Step 4: Monitor

```bash
# Watch logs for agent 1
docker logs -f hodge-agent-1

# Check all agents
for i in $(seq 1 4); do
    echo "=== Agent $i ==="
    docker logs --tail 5 hodge-agent-$i
done

# Check git history (from any agent or host)
cd ~/hodge-upstream
git log --oneline -20
```

### Step 5: Pull results back to your working copy

```bash
cd /path/to/hodge
git pull upstream claude/hodge-conjecture-proof-VSeH8
```

## Agent Specialization (Optional)

For 4+ agents, specialize them by modifying the AGENT_PROMPT.md per container:

| Agent | Role | Prompt Override |
|-------|------|----------------|
| 1 | AlgebraicSupport + SpineBridge | Focus on `AlgebraicSupportImpl.lean` and `SpineBridgeImpl.lean` |
| 2 | Harvey-Lawson | Focus on `HarveyLawsonImpl.lean` |
| 3 | GAGA + Federer-Fleming | Focus on `GAGAImpl.lean` and `FedererFlemingImpl.lean` |
| 4 | Quality + Integration | Review other agents' work, fix merge conflicts, run full builds |

To specialize, mount a custom prompt:
```bash
docker run -d \
    --name hodge-agent-harvey-lawson \
    -e ANTHROPIC_API_KEY=$ANTHROPIC_API_KEY \
    -v ~/hodge-upstream:/upstream \
    -v ~/prompts/harvey_lawson_prompt.md:/workspace/hodge/AGENT_PROMPT.md:ro \
    hodge-agent
```

## Monitoring & Cost Control

### Estimated Costs (claude-opus-4-6)
- ~500K input tokens/session, ~50K output tokens/session
- ~$2-5 per session
- ~4-8 sessions/day/agent
- **Per agent**: ~$10-40/day
- **4 agents**: ~$40-160/day
- **Target timeline**: 2-4 weeks → **$500-4,000 total**

### Kill Switch
```bash
# Stop all agents
docker stop $(docker ps -q --filter name=hodge-agent)

# Or kill a specific agent
docker stop hodge-agent-3
```

### Progress Dashboard
```bash
# From any checkout of the repo
./scripts/verify_progress.sh
```

## Recommended Agent Count by Phase

| Phase | Agents | Why |
|-------|--------|-----|
| **Phase 1** (Foundation) | 3-4 | AlgebraicSupport, GAGA, FedererFleming are independent |
| **Phase 2** (Structure) | 2-3 | HarveyLawson has 3 coupled sorries |
| **Phase 3** (Bridge) | 1-2 | SpineBridge depends on Phase 1+2 |
| **Phase 4** (WIP Cleanup) | 4-8 | Many independent small tasks |

## Troubleshooting

### Merge conflicts
Agents may create merge conflicts. The agent loop pulls before each session,
and Claude can resolve most conflicts. If an agent gets stuck:
```bash
docker restart hodge-agent-N
```

### Build failures
If Mathlib cache is stale:
```bash
docker exec hodge-agent-N bash -c "cd /workspace/hodge && lake exe cache get"
```

### Agent not making progress
Check the logs. If an agent is spinning on a hard sorry:
1. Check `current_tasks/` for lock files
2. Remove stale locks: `docker exec hodge-agent-N rm /workspace/hodge/current_tasks/stuck_task.txt`
3. Update PROGRESS.md with the failed approach so other agents avoid it
