#!/usr/bin/env python3
"""
Parallel Proof Agents - Multiple agents working on different files simultaneously.

This script spawns multiple worker threads, each targeting a different file.
A central coordinator ensures:
1. No two agents work on the same file
2. All changes maintain a green build
3. Trivializations are rejected

Safe parallelization strategy:
- Each agent claims a file exclusively
- Changes are tested before committing
- Build lock prevents concurrent builds
"""

import os
import re
import subprocess
import json
import time
import datetime
import urllib.request
import threading
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from queue import Queue
import random

# Configuration
ANTHROPIC_API_KEY = os.environ.get("ANTHROPIC_API_KEY", "")
SLACK_WEBHOOK = os.environ.get("SLACK_WEBHOOK", "")
MODEL = "claude-opus-4-5-20251101"
REPO_PATH = Path("/home/ubuntu/hodge")
LOG_DIR = REPO_PATH / "autonomous_logs"
LAKE_PATH = "/home/ubuntu/.elan/bin/lake"
PROOF_HINTS_PATH = REPO_PATH / "scripts" / "agents" / "PROOF_HINTS.md"

# How many recent rejections to show the model as "do not do this".
MAX_RECENT_REJECTIONS = 5

# Number of parallel agents
NUM_AGENTS = 10

# All files with sorries (will work through these)
ALL_TARGET_FILES = [
    "Hodge/Analytic/FlatNormReal.lean",
    "Hodge/Analytic/Integration/SubmanifoldIntegral.lean",
    "Hodge/GMT/FlatNorm.lean",
    "Hodge/GMT/Mass.lean",
    "Hodge/GMT/Calibration.lean",
    "Hodge/Analytic/Stage2/IntegrationCurrentsManifoldSkeleton.lean",
    "Hodge/Analytic/Integration/Stokes.lean",
    "Hodge/Classical/CycleClass.lean",
    "Hodge/Classical/GAGA.lean",
    "Hodge/Analytic/Advanced.lean",
    "Hodge/Analytic/IntegralCurrents.lean",
    "Hodge/Kahler/Main.lean",
]

# FORBIDDEN patterns - trivializations
FORBIDDEN_PATTERNS = [
    r':=\s*trivial\s*$',
    r':=\s*True\s*$',
    r':=\s*True\.intro\s*$',
    r':\s*True\s*:=',
    r':=\s*⟨⟩\s*$',
    r'\badmit\b',
]

# Thread-safe resources
build_lock = threading.Lock()
file_locks = {f: threading.Lock() for f in ALL_TARGET_FILES}
stats_lock = threading.Lock()
log_lock = threading.Lock()
rejection_lock = threading.Lock()

# Shared stats
stats = {
    "start_time": None,
    "sorries_eliminated": 0,
    "failed_attempts": 0,
    "rejected_trivializations": 0,
    "agents_active": 0,
    "last_slack_update": 0,
}

# Adaptive per-file rejection memory (updated when a candidate proof is rejected).
LAST_REJECTION_NOTE = {}
RECENT_REJECTIONS = []  # list of dicts (bounded)

def load_proof_hints() -> str:
    try:
        return PROOF_HINTS_PATH.read_text()
    except Exception:
        return ""

PROOF_HINTS_TEXT = load_proof_hints()

def log(msg, agent_id=None):
    """Thread-safe logging."""
    ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    prefix = f"[Agent-{agent_id}]" if agent_id is not None else "[Main]"
    line = f"[{ts}] {prefix} {msg}"
    with log_lock:
        print(line, flush=True)
        try:
            with open(LOG_DIR / "parallel.log", "a") as f:
                f.write(line + "\n")
        except:
            pass

def slack_notify(msg):
    """Send Slack notification."""
    try:
        data = json.dumps({"text": msg}).encode()
        req = urllib.request.Request(SLACK_WEBHOOK, data=data,
                                      headers={"Content-Type": "application/json"})
        urllib.request.urlopen(req, timeout=10)
    except Exception as e:
        log(f"Slack error: {e}")

def run_cmd(cmd, timeout=300):
    """Run shell command."""
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True,
                                text=True, timeout=timeout, cwd=REPO_PATH)
        return result.returncode == 0, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return False, "Timeout"
    except Exception as e:
        return False, str(e)

def count_sorries(filepath):
    """Count sorries in a file."""
    try:
        content = (REPO_PATH / filepath).read_text()
        pattern = r'(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])'
        lines = content.splitlines()
        return sum(1 for line in lines
                   if re.search(pattern, line) and not line.strip().startswith('--'))
    except:
        return -1

def get_total_sorries():
    """Get total sorry count."""
    return sum(max(0, count_sorries(f)) for f in ALL_TARGET_FILES)

def classify_rejection(code: str):
    """Return (is_rejected: bool, reason: str)."""
    for pattern in FORBIDDEN_PATTERNS:
        if re.search(pattern, code, re.IGNORECASE):
            return True, f"matches forbidden pattern `{pattern}`"
    if ':= trivial' in code.lower() or ':= true' in code.lower():
        return True, "contains ':= trivial' or ':= true'"
    return False, ""

def note_rejection(filepath: str, agent_id: int, reason: str, snippet: str):
    """Record a rejection and update per-file feedback."""
    ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    snippet = snippet.strip()
    if len(snippet) > 240:
        snippet = snippet[:240] + "…"
    entry = {"time": ts, "file": filepath, "agent": agent_id, "reason": reason, "snippet": snippet}
    with rejection_lock:
        LAST_REJECTION_NOTE[filepath] = f"Last attempt was rejected: {reason}. Offending snippet: {snippet!r}"
        RECENT_REJECTIONS.append(entry)
        if len(RECENT_REJECTIONS) > MAX_RECENT_REJECTIONS:
            del RECENT_REJECTIONS[0]

def rejection_feedback_for(filepath: str) -> str:
    with rejection_lock:
        note = LAST_REJECTION_NOTE.get(filepath, "")
        recent = list(RECENT_REJECTIONS)
    blocks = []
    if note:
        blocks.append(f"RECENT REJECTION FOR THIS FILE:\n- {note}")
    if recent:
        blocks.append("RECENT REJECTIONS (DO NOT REPEAT THESE PATTERNS):\n" + "\n".join(
            [f"- {e['file']}: {e['reason']} | {e['snippet']}" for e in recent]
        ))
    return "\n\n".join(blocks).strip()

def find_first_sorry(filepath):
    """Find first sorry in file with context."""
    try:
        content = (REPO_PATH / filepath).read_text()
        lines = content.splitlines()
        pattern = r'(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])'
        
        for i, line in enumerate(lines):
            if re.search(pattern, line) and not line.strip().startswith('--'):
                start = max(0, i - 30)
                end = min(len(lines), i + 15)
                context = '\n'.join(f"{j+1}|{lines[j]}" for j in range(start, end))
                return i + 1, line, context
        return None, None, None
    except:
        return None, None, None

def call_claude(prompt, agent_id):
    """Call Claude API."""
    try:
        data = json.dumps({
            "model": MODEL,
            "max_tokens": 4096,
            "messages": [{"role": "user", "content": prompt}]
        }).encode()
        
        req = urllib.request.Request(
            "https://api.anthropic.com/v1/messages",
            data=data,
            headers={
                "Content-Type": "application/json",
                "x-api-key": ANTHROPIC_API_KEY,
                "anthropic-version": "2023-06-01"
            }
        )
        
        with urllib.request.urlopen(req, timeout=120) as resp:
            result = json.loads(resp.read().decode())
            return result["content"][0]["text"]
    except Exception as e:
        log(f"API error: {e}", agent_id)
        return None

def build_file(filepath):
    """Build a specific file. Uses build lock for safety."""
    module = filepath.replace('/', '.').replace('.lean', '')
    with build_lock:
        ok, output = run_cmd(
            f"export PATH=/home/ubuntu/.elan/bin:$PATH && {LAKE_PATH} build {module} 2>&1 | tail -10",
            timeout=180
        )
        return "error" not in output.lower() or "Build completed" in output, output

def attempt_proof(filepath, line_num, line_content, context, agent_id):
    """Attempt to prove one sorry."""
    feedback = rejection_feedback_for(filepath)
    hints = PROOF_HINTS_TEXT
    hints_block = f"PROOF HINTS:\n{hints}\n" if hints else ""
    feedback_block = f"FEEDBACK:\n{feedback}\n" if feedback else ""
    prompt = f"""You are proving lemmas in a Lean 4 Hodge Conjecture formalization.

File: {filepath}
Line {line_num}: {line_content}

Context:
```lean
{context}
```

{hints_block}{feedback_block}

RULES:
1. Replace the `sorry` with a REAL Lean 4 proof
2. DO NOT use: `:= trivial`, `:= True`, `True.intro`, `⟨⟩`, or `admit`
3. Use proper tactics: `simp`, `exact`, `apply`, `intro`, `constructor`, etc.

Respond with ONLY JSON:
{{"old_code": "exact line with sorry", "new_code": "replacement with proof"}}
"""
    
    response = call_claude(prompt, agent_id)
    if not response:
        return False
    
    try:
        match = re.search(r'\{[^{}]*"old_code"[^{}]*"new_code"[^{}]*\}', response, re.DOTALL)
        if not match:
            return False
        
        data = json.loads(match.group())
        old_code = data.get("old_code", "")
        new_code = data.get("new_code", "")
        
        if not old_code or not new_code:
            return False
        
        rejected, reason = classify_rejection(new_code)
        if rejected:
            with stats_lock:
                stats["rejected_trivializations"] += 1
            note_rejection(filepath, agent_id, reason, new_code)
            log(f"REJECTED candidate proof ({reason})", agent_id)
            return False
        
        # Apply change
        full_path = REPO_PATH / filepath
        content = full_path.read_text()
        
        if old_code not in content:
            return False
        
        new_content = content.replace(old_code, new_code, 1)
        full_path.write_text(new_content)
        
        # Test build
        ok, output = build_file(filepath)
        
        if ok and "sorry" not in new_code.lower():
            log(f"✅ SUCCESS at {filepath}:{line_num}", agent_id)
            with stats_lock:
                stats["sorries_eliminated"] += 1
            return True
        else:
            # Revert
            full_path.write_text(content)
            with stats_lock:
                stats["failed_attempts"] += 1
            return False
            
    except Exception as e:
        log(f"Error: {e}", agent_id)
        return False

def agent_worker(agent_id, file_queue):
    """Worker thread for one agent."""
    log(f"Starting", agent_id)
    
    with stats_lock:
        stats["agents_active"] += 1
    
    try:
        while True:
            # Get a file to work on
            try:
                filepath = file_queue.get(timeout=5)
            except:
                # Check if more work exists
                for f in ALL_TARGET_FILES:
                    if count_sorries(f) > 0:
                        file_queue.put(f)
                continue
            
            # Acquire exclusive lock on this file
            if not file_locks[filepath].acquire(blocking=False):
                file_queue.put(filepath)  # Put back for another agent
                time.sleep(0.5)
                continue
            
            try:
                sorry_count = count_sorries(filepath)
                if sorry_count <= 0:
                    continue
                
                log(f"Working on {filepath} ({sorry_count} sorries)", agent_id)
                
                # Work on first sorry
                line_num, line_content, context = find_first_sorry(filepath)
                if line_num:
                    attempt_proof(filepath, line_num, line_content, context, agent_id)
                
                # Put file back if more sorries remain
                if count_sorries(filepath) > 0:
                    file_queue.put(filepath)
                    
            finally:
                file_locks[filepath].release()
            
            time.sleep(1)  # Brief pause between attempts
            
    except Exception as e:
        log(f"Worker error: {e}", agent_id)
    finally:
        with stats_lock:
            stats["agents_active"] -= 1
        log(f"Stopping", agent_id)

def progress_monitor():
    """Monitor and report progress."""
    while True:
        time.sleep(300)  # Every 5 minutes
        
        total = get_total_sorries()
        elapsed = (time.time() - stats["start_time"]) / 3600
        
        with stats_lock:
            eliminated = stats["sorries_eliminated"]
            failed = stats["failed_attempts"]
            rejected = stats["rejected_trivializations"]
            active = stats["agents_active"]
        
        rate = eliminated / elapsed if elapsed > 0 else 0
        
        msg = f"""📊 *Parallel Agents Progress*
• Agents active: {active}/{NUM_AGENTS}
• Elapsed: {elapsed:.1f} hours
• Eliminated: {eliminated} sorries
• Failed: {failed}, Rejected: {rejected}
• Remaining: {total}
• Rate: {rate:.1f}/hour"""
        
        log(f"Status: {eliminated} eliminated, {total} remaining, {active} agents active")
        
        # Hourly Slack update
        if time.time() - stats["last_slack_update"] > 3600:
            slack_notify(msg)
            stats["last_slack_update"] = time.time()
        
        if total == 0:
            slack_notify("🎉 *PROOF COMPLETE!* All sorries eliminated!")
            break

def main():
    """Main entry point."""
    LOG_DIR.mkdir(exist_ok=True)
    
    # Ensure we never rebuild Mathlib from source.
    # (Fetch precompiled cache once before any build attempts.)
    log("Fetching Mathlib cache (lake exe cache get)…")
    ok, out = run_cmd(f"export PATH=/home/ubuntu/.elan/bin:$PATH && {LAKE_PATH} exe cache get", timeout=900)
    log("Mathlib cache ready" if ok else f"Mathlib cache fetch failed (continuing): {out[-200:]}")

    log("=" * 60)
    log(f"PARALLEL PROOF AGENTS STARTING ({NUM_AGENTS} agents)")
    log("=" * 60)
    
    stats["start_time"] = time.time()
    stats["last_slack_update"] = time.time()
    
    total = get_total_sorries()
    slack_notify(f"🚀 *Parallel Proof System Started*\n• Agents: {NUM_AGENTS}\n• Target files: {len(ALL_TARGET_FILES)}\n• Initial sorries: {total}")
    
    # Initialize work queue with all files that have sorries
    file_queue = Queue()
    for f in ALL_TARGET_FILES:
        if count_sorries(f) > 0:
            file_queue.put(f)
    
    # Start monitor thread
    monitor = threading.Thread(target=progress_monitor, daemon=True)
    monitor.start()
    
    # Start agent workers
    with ThreadPoolExecutor(max_workers=NUM_AGENTS) as executor:
        futures = [executor.submit(agent_worker, i, file_queue) for i in range(NUM_AGENTS)]
        
        try:
            # Wait for completion or interrupt
            for future in as_completed(futures):
                try:
                    future.result()
                except Exception as e:
                    log(f"Agent failed: {e}")
        except KeyboardInterrupt:
            log("Interrupted")
    
    log("All agents stopped")
    slack_notify("🛑 Parallel proof system stopped")

if __name__ == "__main__":
    main()
