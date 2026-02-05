#!/bin/bash
# =============================================================================
# monitor.sh — Remote monitoring dashboard for Hodge proof agents
# =============================================================================
# Run from your Mac:
#   ./scripts/monitor.sh          # One-shot status check
#   ./scripts/monitor.sh --watch  # Continuous monitoring (every 60s)
#   ./scripts/monitor.sh --logs N # Tail agent N's latest log
#   ./scripts/monitor.sh --attach # Attach to tmux session

SERVER="129.146.121.60"
SSH_KEY="$HOME/Projects/straight-shot/lambda-b200-private-key"
SSH_USER="${SSH_USER:-ubuntu}"
SSH_CMD="ssh -i $SSH_KEY -o StrictHostKeyChecking=no ${SSH_USER}@${SERVER}"
BRANCH="claude/hodge-conjecture-proof-VSeH8"

case "${1:-status}" in
    --watch|-w)
        while true; do
            clear
            echo "=== Hodge Proof Agent Monitor ($(date)) ==="
            echo ""
            $SSH_CMD "bash -s" <<'EOF'
export PATH="$HOME/.elan/bin:$PATH"
cd ~/hodge-workspace/hodge
git pull upstream claude/hodge-conjecture-proof-VSeH8 --no-edit 2>/dev/null

echo "--- Git Log (last 10 commits) ---"
git log --oneline -10
echo ""

echo "--- Sorry Count ---"
./scripts/verify_progress.sh 2>/dev/null
echo ""

echo "--- Active Agents ---"
for d in ~/hodge-workspace/agent_*/; do
    if [ -d "$d" ]; then
        agent=$(basename $d)
        latest=$(ls -t ${d}logs/*.log 2>/dev/null | head -1)
        if [ -n "$latest" ]; then
            age=$(( ($(date +%s) - $(stat -c %Y "$latest")) / 60 ))
            last_line=$(tail -1 "$latest" 2>/dev/null)
            echo "  $agent: last activity ${age}m ago"
        fi
    fi
done
echo ""

echo "--- Task Locks ---"
ls -la ~/hodge-workspace/hodge/current_tasks/ 2>/dev/null || echo "  (none)"
EOF
            echo ""
            echo "(refreshing every 60s — Ctrl+C to stop)"
            sleep 60
        done
        ;;

    --logs|-l)
        AGENT_NUM="${2:-1}"
        echo "Tailing agent ${AGENT_NUM} latest log..."
        $SSH_CMD "tail -f \$(ls -t ~/hodge-workspace/agent_${AGENT_NUM}/logs/*.log 2>/dev/null | head -1)"
        ;;

    --attach|-a)
        echo "Attaching to tmux session..."
        $SSH_CMD -t "tmux attach -t hodge"
        ;;

    --stop)
        echo "Stopping all agents..."
        $SSH_CMD "tmux kill-session -t hodge 2>/dev/null; echo 'Agents stopped.'"
        ;;

    --restart)
        echo "Restarting agents..."
        $SSH_CMD "tmux kill-session -t hodge 2>/dev/null; cd ~/hodge-workspace && ./run_agents.sh ${2:-8}"
        ;;

    *)
        echo "=== Hodge Proof Status ==="
        $SSH_CMD "bash -s" <<'EOF'
export PATH="$HOME/.elan/bin:$PATH"
cd ~/hodge-workspace/hodge 2>/dev/null || { echo "Workspace not set up. Run deploy_agents.sh first."; exit 1; }
git pull upstream claude/hodge-conjecture-proof-VSeH8 --no-edit 2>/dev/null
echo ""
git log --oneline -5
echo ""
./scripts/verify_progress.sh 2>/dev/null
EOF
        ;;
esac
