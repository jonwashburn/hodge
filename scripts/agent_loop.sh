#!/bin/bash
# Autonomous agent loop for Hodge Conjecture formalization
# Based on Anthropic's agent teams methodology
# https://www.anthropic.com/engineering/building-c-compiler
#
# Usage:
#   ./scripts/agent_loop.sh [--agents N] [--model MODEL]
#
# This script runs Claude in an infinite loop, where each iteration:
# 1. Pulls latest changes from upstream
# 2. Runs Claude with AGENT_PROMPT.md
# 3. Logs output
# 4. Repeats
#
# Run this inside a Docker container (recommended) or tmux session.
# IMPORTANT: Use --dangerously-skip-permissions only in sandboxed containers.

set -euo pipefail

AGENTS=${AGENTS:-1}
MODEL=${MODEL:-claude-opus-4-6}
BRANCH="claude/hodge-conjecture-proof-VSeH8"
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LOG_DIR="${REPO_ROOT}/agent_logs"

mkdir -p "$LOG_DIR"
mkdir -p "${REPO_ROOT}/current_tasks"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --agents) AGENTS="$2"; shift 2 ;;
        --model) MODEL="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

run_agent() {
    local agent_id=$1
    local agent_log_dir="${LOG_DIR}/agent_${agent_id}"
    mkdir -p "$agent_log_dir"

    echo "[Agent ${agent_id}] Starting autonomous loop..."

    while true; do
        COMMIT=$(cd "$REPO_ROOT" && git rev-parse --short=6 HEAD)
        TIMESTAMP=$(date +%Y%m%d_%H%M%S)
        LOGFILE="${agent_log_dir}/session_${TIMESTAMP}_${COMMIT}.log"

        echo "[Agent ${agent_id}] Starting session at commit ${COMMIT}..."
        echo "[Agent ${agent_id}] Log: ${LOGFILE}"

        # Pull latest changes
        cd "$REPO_ROOT"
        git pull origin "$BRANCH" --no-edit 2>/dev/null || true

        # Run Claude
        claude --dangerously-skip-permissions \
               -p "$(cat AGENT_PROMPT.md)" \
               --model "$MODEL" \
               &> "$LOGFILE" || true

        echo "[Agent ${agent_id}] Session complete. Checking progress..."

        # Quick progress check
        ./scripts/verify_progress.sh 2>&1 | tail -5 >> "$LOGFILE"

        # Brief pause between sessions
        sleep 5
    done
}

# Launch agents
echo "============================================"
echo "Hodge Conjecture Autonomous Agent Harness"
echo "============================================"
echo "Agents: ${AGENTS}"
echo "Model: ${MODEL}"
echo "Branch: ${BRANCH}"
echo "Log dir: ${LOG_DIR}"
echo "============================================"

if [ "$AGENTS" -eq 1 ]; then
    run_agent 0
else
    for i in $(seq 0 $((AGENTS - 1))); do
        run_agent "$i" &
        sleep 2  # Stagger starts
    done
    wait
fi
