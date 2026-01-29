#!/usr/bin/env python3
"""
Notification System for Autonomous Hodge Proof
- Slack webhooks for progress updates
- Health monitoring and stuck detection
- Git auto-commit and push
"""

import os
import json
import asyncio
import aiohttp
from datetime import datetime, timedelta
from pathlib import Path
from typing import Optional, Dict, Any
import subprocess

# Configuration
HODGE_PATH = Path("/home/ubuntu/hodge")
STATE_FILE = HODGE_PATH / "autonomous_state.json"
HEALTH_FILE = HODGE_PATH / "health_state.json"

# Slack webhook - will be set via environment or file
def get_slack_webhook():
    webhook = os.environ.get("SLACK_WEBHOOK_URL", "").strip()
    if webhook:
        return webhook
    webhook_file = Path.home() / ".hodge_slack_webhook"
    if webhook_file.exists():
        return webhook_file.read_text().strip()
    return ""

SLACK_WEBHOOK = get_slack_webhook()

# Notification intervals
PROGRESS_INTERVAL = timedelta(minutes=30)  # Progress update every 30 min
HEALTH_CHECK_INTERVAL = timedelta(minutes=10)  # Health check every 10 min
STUCK_THRESHOLD = timedelta(minutes=20)  # Alert if no progress for 20 min

class NotificationSystem:
    def __init__(self):
        self.last_progress_update = datetime.now()
        self.last_health_check = datetime.now()
        self.last_task_count = 0
        self.health_state = self._load_health_state()
    
    def _load_health_state(self) -> Dict[str, Any]:
        if HEALTH_FILE.exists():
            try:
                return json.loads(HEALTH_FILE.read_text())
            except:
                pass
        return {"last_completed": 0, "last_check": datetime.now().isoformat()}
    
    def _save_health_state(self):
        HEALTH_FILE.write_text(json.dumps(self.health_state, indent=2))
    
    async def send_slack(self, message: str, emoji: str = "🔔", urgent: bool = False):
        """Send a message to Slack."""
        if not SLACK_WEBHOOK:
            print(f"[Slack disabled] {message}")
            return
        
        payload = {
            "text": f"{emoji} *Hodge Proof*: {message}",
            "unfurl_links": False
        }
        
        if urgent:
            payload["text"] = f"🚨 *URGENT* {payload['text']}"
        
        try:
            async with aiohttp.ClientSession() as session:
                await session.post(SLACK_WEBHOOK, json=payload, timeout=10)
        except Exception as e:
            print(f"Slack error: {e}")
    
    def get_task_stats(self) -> Dict[str, int]:
        """Get current task statistics."""
        if not STATE_FILE.exists():
            return {}
        
        try:
            data = json.loads(STATE_FILE.read_text())
            tasks = data.get("tasks", [])
            stats = {
                "total": len(tasks),
                "completed": sum(1 for t in tasks if t.get("status") == "completed"),
                "in_progress": sum(1 for t in tasks if t.get("status") == "in_progress"),
                "pending": sum(1 for t in tasks if t.get("status") == "pending"),
                "failed": sum(1 for t in tasks if t.get("status") == "failed"),
            }
            return stats
        except:
            return {}
    
    async def check_health(self):
        """Check if agents are healthy and making progress."""
        stats = self.get_task_stats()
        if not stats:
            return
        
        completed = stats.get("completed", 0)
        in_progress = stats.get("in_progress", 0)
        
        # Check for stuck state
        last_completed = self.health_state.get("last_completed", 0)
        last_check_str = self.health_state.get("last_check", datetime.now().isoformat())
        last_check = datetime.fromisoformat(last_check_str)
        
        now = datetime.now()
        time_since_check = now - last_check
        
        # If no progress in STUCK_THRESHOLD, alert
        if completed == last_completed and time_since_check > STUCK_THRESHOLD and in_progress > 0:
            await self.send_slack(
                f"⚠️ No progress in {int(time_since_check.total_seconds() / 60)} minutes! "
                f"{in_progress} tasks stuck in progress. "
                f"Completed: {completed}/{stats['total']}",
                emoji="⚠️",
                urgent=True
            )
        
        # Update health state if progress was made
        if completed > last_completed:
            self.health_state["last_completed"] = completed
            self.health_state["last_check"] = now.isoformat()
            self._save_health_state()
            
            # Celebrate milestones
            if completed % 10 == 0:
                await self.send_slack(
                    f"🎉 Milestone: {completed} tasks completed!",
                    emoji="🎉"
                )
    
    async def send_progress_update(self):
        """Send periodic progress update."""
        stats = self.get_task_stats()
        if not stats:
            return
        
        pct = (stats["completed"] / stats["total"] * 100) if stats["total"] > 0 else 0
        
        await self.send_slack(
            f"📊 Progress Update:\n"
            f"• Completed: {stats['completed']}/{stats['total']} ({pct:.1f}%)\n"
            f"• In Progress: {stats['in_progress']}\n"
            f"• Failed: {stats['failed']}",
            emoji="📊"
        )
    
    async def notify_completion(self):
        """Notify when proof is complete."""
        await self.send_slack(
            "🏆 *PROOF COMPLETE!* 🏆\n"
            "The Hodge Conjecture formalization has been completed!\n"
            "All tasks finished. Check the repository for the final proof.",
            emoji="🏆",
            urgent=True
        )
    
    async def notify_failure(self, task_id: str, error: str):
        """Notify on task failure."""
        await self.send_slack(
            f"❌ Task failed: `{task_id}`\n"
            f"Error: {error[:200]}",
            emoji="❌"
        )


class GitSync:
    """Handles automatic git commits and pushes."""
    
    def __init__(self):
        self.last_commit = datetime.now()
        self.commit_interval = timedelta(minutes=15)
    
    def run_git(self, *args) -> tuple[bool, str]:
        """Run a git command."""
        try:
            result = subprocess.run(
                ["git"] + list(args),
                cwd=str(HODGE_PATH),
                capture_output=True,
                text=True,
                timeout=60
            )
            return result.returncode == 0, result.stdout + result.stderr
        except Exception as e:
            return False, str(e)
    
    def has_changes(self) -> bool:
        """Check if there are uncommitted changes."""
        ok, output = self.run_git("status", "--porcelain")
        return ok and bool(output.strip())
    
    def commit_and_push(self, message: str = None) -> tuple[bool, str]:
        """Commit all changes and push."""
        if not self.has_changes():
            return True, "No changes to commit"
        
        # Add all Lean files
        self.run_git("add", "Hodge/", "*.lean")
        
        # Commit
        if message is None:
            stats = NotificationSystem().get_task_stats()
            completed = stats.get("completed", 0)
            total = stats.get("total", 0)
            message = f"[auto] Progress: {completed}/{total} tasks complete"
        
        ok, output = self.run_git("commit", "-m", message)
        if not ok:
            return False, f"Commit failed: {output}"
        
        # Push
        ok, output = self.run_git("push")
        if not ok:
            return False, f"Push failed: {output}"
        
        return True, "Committed and pushed successfully"
    
    async def auto_sync(self, notifier: NotificationSystem):
        """Periodically commit and push changes."""
        now = datetime.now()
        if now - self.last_commit < self.commit_interval:
            return
        
        if self.has_changes():
            ok, msg = self.commit_and_push()
            self.last_commit = now
            
            if ok:
                print(f"[Git] {msg}")
            else:
                await notifier.send_slack(f"⚠️ Git sync failed: {msg}", urgent=True)


async def monitor_loop():
    """Main monitoring loop."""
    notifier = NotificationSystem()
    git = GitSync()
    
    print("Starting notification and sync monitor...")
    await notifier.send_slack("🚀 Autonomous proof system started!", emoji="🚀")
    
    while True:
        try:
            # Health check
            await notifier.check_health()
            
            # Progress update
            now = datetime.now()
            if now - notifier.last_progress_update > PROGRESS_INTERVAL:
                await notifier.send_progress_update()
                notifier.last_progress_update = now
            
            # Git sync
            await git.auto_sync(notifier)
            
            # Check for completion
            stats = notifier.get_task_stats()
            if stats.get("total", 0) > 0 and stats.get("pending", 1) == 0 and stats.get("in_progress", 1) == 0:
                if stats.get("completed", 0) == stats.get("total", 0):
                    await notifier.notify_completion()
                    git.commit_and_push("[complete] Hodge Conjecture proof finalized")
                    break
            
            await asyncio.sleep(60)  # Check every minute
            
        except Exception as e:
            print(f"Monitor error: {e}")
            await asyncio.sleep(60)


if __name__ == "__main__":
    asyncio.run(monitor_loop())
