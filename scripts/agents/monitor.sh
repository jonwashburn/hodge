#!/bin/bash
# Monitor the Hodge Agent Coordinator on Lambda Labs B200

SERVER="ubuntu@192.222.59.220"
SSH_KEY="$HOME/.ssh/lambda-b200"
REMOTE_HODGE="/home/ubuntu/hodge"

case "${1:-status}" in
    status)
        echo "=== Agent Status ==="
        ssh -i "$SSH_KEY" "$SERVER" "cd $REMOTE_HODGE && python3 scripts/agents/coordinator.py status"
        ;;
    logs)
        echo "=== Coordinator Logs ==="
        ssh -i "$SSH_KEY" "$SERVER" "tail -100 $REMOTE_HODGE/agent_coordinator.log"
        ;;
    follow)
        echo "=== Following Logs (Ctrl+C to stop) ==="
        ssh -i "$SSH_KEY" "$SERVER" "tail -f $REMOTE_HODGE/agent_coordinator.log"
        ;;
    agent-logs)
        echo "=== Recent Agent Logs ==="
        ssh -i "$SSH_KEY" "$SERVER" "ls -lt $REMOTE_HODGE/agent_logs | head -20"
        ;;
    read)
        if [ -z "$2" ]; then
            echo "Usage: ./monitor.sh read <log_file>"
            exit 1
        fi
        ssh -i "$SSH_KEY" "$SERVER" "cat $REMOTE_HODGE/agent_logs/$2"
        ;;
    stop)
        echo "Stopping coordinator..."
        ssh -i "$SSH_KEY" "$SERVER" "pkill -f 'python3.*coordinator.py' || echo 'Not running'"
        ;;
    shell)
        echo "Opening shell on server..."
        ssh -i "$SSH_KEY" "$SERVER"
        ;;
    *)
        echo "Usage: ./monitor.sh [status|logs|follow|agent-logs|read <file>|stop|shell]"
        ;;
esac
