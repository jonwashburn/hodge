#!/usr/bin/env python3
"""
OpenAI Proof Agent (Responses API)

Primary model (configurable):
- OPENAI_MODEL (default: gpt-5.2-high)

Fallback models (comma-separated):
- OPENAI_FALLBACK_MODELS (default: gpt-5.2-codex,gpt-4o)

Notes:
- Some models (e.g. gpt-5.2-codex) do not support `temperature`. We omit it for those.
- We use the OpenAI Responses API (`/v1/responses`) for maximum model compatibility.
- Trivializations are rejected (:= trivial / := True / True.intro / ⟨⟩, etc).
"""

import os
import re
import subprocess
import json
import time
import datetime
import urllib.request
import urllib.error
import threading
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from queue import Queue

# Configuration
OPENAI_API_KEY = os.environ.get("OPENAI_API_KEY", "")
SLACK_WEBHOOK = os.environ.get("SLACK_WEBHOOK", "")
MODEL = os.environ.get("OPENAI_MODEL", "gpt-5.2")

# Number of parallel agents
NUM_AGENTS = int(os.environ.get("NUM_AGENTS", "8"))
FALLBACK_MODELS = [
    m.strip() for m in os.environ.get("OPENAI_FALLBACK_MODELS", "gpt-5.2-codex,gpt-4o").split(",")
    if m.strip()
]
REPO_PATH = Path("/home/ubuntu/hodge")
LOG_DIR = REPO_PATH / "autonomous_logs"
LAKE_PATH = "/home/ubuntu/.elan/bin/lake"

# Target files with remaining sorries (priority order)
# Keep this list tight: only files with actual `sorry` on the main path.
TARGET_FILES = [
    "Hodge/Kahler/Main.lean",
    # Optional scaffold file (not usually in the dependency cone of the main theorem):
    "Hodge/Analytic/Stage2/IntegrationCurrentsManifoldSkeleton.lean",
]

# FORBIDDEN patterns - trivializations
FORBIDDEN_PATTERNS = [
    r':=\s*trivial\b',
    r':=\s*True\b',
    r':=\s*True\.intro\b',
    r':\s*True\s*:=',
    r':=\s*⟨⟩\s*$',
    r'\badmit\b',
]

# Proof hints discovered during manual work
AGENT_CONTEXT_PATH = REPO_PATH / "scripts" / "agents" / "AGENT_CONTEXT.md"
PROOF_HINTS_PATH = REPO_PATH / "scripts" / "agents" / "PROOF_HINTS.md"

PLACEHOLDER_DEFINITIONS = """
## KEY DEFINITIONS (PHASE‑1 FUNCTIONAL‑ANALYTIC LAYER)

1) Smooth forms are NOT discrete:
   - `SmoothForm n X k` is seminormed/Normed over ℝ with `‖ω‖ = comass ω`.
   - Do NOT use `continuous_of_discreteTopology`.

2) Currents are continuous linear functionals:
   - `Current n X k` has `toFun : SmoothForm n X k →L[ℝ] ℝ`.
   - Boundedness comes from opNorm; there is no per-current `bound` field.
   - Only extra hypothesis stored is `boundary_bound` (controls `ω ↦ T(dω)`).

3) Deep axioms still present (do not “fake-prove”):
   - `Hodge/Classical/GAGA.lean`: `fundamental_eq_representing_axiom`
   - `Hodge/Analytic/Integration/SubmanifoldIntegral.lean`: `opaque submanifoldIntegral` + axioms about add/smul/continuity
"""

def load_agent_context():
    try:
        return AGENT_CONTEXT_PATH.read_text()
    except Exception:
        return ""

AGENT_CONTEXT_TEXT = load_agent_context()

def load_proof_hints():
    try:
        return PROOF_HINTS_PATH.read_text()
    except Exception:
        return ""

PROOF_HINTS_TEXT = load_proof_hints()

stats = {
    "start_time": None,
    "sorries_eliminated": 0,
    "failed_attempts": 0,
    "rejected_trivializations": 0,
    "agents_active": 0,
}

# Thread-safe resources
build_lock = threading.Lock()
stats_lock = threading.Lock()
log_lock = threading.Lock()
file_locks = {f: threading.Lock() for f in TARGET_FILES}

NO_TEMPERATURE_MODELS = {
    # Returns 400: "Unsupported parameter: 'temperature' is not supported with this model."
    "gpt-5.2",
    "gpt-5.2-codex",
}

DISABLED_MODELS = set()

MAX_OUTPUT_TOKENS_BY_MODEL = {
    # gpt-5.2 with reasoning.effort=high uses lots of reasoning tokens; give it maximum room.
    "gpt-5.2": 100000,
    # Codex often needs more room to return a full JSON object with Lean code.
    "gpt-5.2-codex": 32000,
}
DEFAULT_MAX_OUTPUT_TOKENS = 4096

REASONING_EFFORT_BY_MODEL = {
    # gpt-5.2 supports reasoning.effort; "high" for deepest thinking on hard proofs.
    "gpt-5.2": "high",
    # Keep codex reasoning cheap so we don't burn max_output_tokens before producing JSON.
    "gpt-5.2-codex": "low",
}

# Timeout per model (seconds). gpt-5.2 with high reasoning can take very long.
TIMEOUT_BY_MODEL = {
    "gpt-5.2": 5000,  # ~83 minutes for high reasoning effort
    "gpt-5.2-codex": 600,
}
DEFAULT_TIMEOUT = 300

JSON_SCHEMA_FORMAT = {
    "type": "json_schema",
    "name": "proof_edit",
    "schema": {
        "type": "object",
        "additionalProperties": False,
        "properties": {
            "old_code": {"type": "string"},
            "new_code": {"type": "string"},
        },
        "required": ["old_code", "new_code"],
    },
}

def log(msg, agent_id=None):
    ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    prefix = f"[GPT-{agent_id}]" if agent_id is not None else "[OpenAI]"
    line = f"[{ts}] {prefix} {msg}"
    with log_lock:
        print(line, flush=True)

def slack_notify(msg):
    try:
        data = json.dumps({"text": msg}).encode()
        req = urllib.request.Request(SLACK_WEBHOOK, data=data,
                                      headers={"Content-Type": "application/json"})
        urllib.request.urlopen(req, timeout=10)
    except Exception as e:
        log(f"Slack error: {e}")

def run_cmd(cmd, timeout=300):
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True,
                                text=True, timeout=timeout, cwd=REPO_PATH)
        return result.returncode == 0, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return False, "Timeout"
    except Exception as e:
        return False, str(e)

def count_sorries(filepath):
    try:
        content = (REPO_PATH / filepath).read_text()
        pattern = r'(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])'
        lines = content.splitlines()
        return sum(1 for line in lines
                   if re.search(pattern, line) and not line.strip().startswith('--'))
    except:
        return -1

def get_total_sorries():
    return sum(max(0, count_sorries(f)) for f in TARGET_FILES)

def is_trivialization(code):
    for pattern in FORBIDDEN_PATTERNS:
        if re.search(pattern, code, re.IGNORECASE):
            return True
    return False

def find_first_sorry(filepath):
    """Find first sorry with FULL FILE CONTEXT."""
    try:
        content = (REPO_PATH / filepath).read_text()
        lines = content.splitlines()
        pattern = r'(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])'
        
        for i, line in enumerate(lines):
            if re.search(pattern, line) and not line.strip().startswith('--'):
                # FULL FILE with line numbers
                full_context = '\n'.join(f"{j+1}|{lines[j]}" for j in range(len(lines)))
                
                # Focused context around sorry
                start = max(0, i - 40)
                end = min(len(lines), i + 20)
                focused_context = '\n'.join(f"{j+1}|{lines[j]}" for j in range(start, end))
                
                return i + 1, line, full_context, focused_context
        return None, None, None, None
    except:
        return None, None, None, None

def call_openai(prompt):
    """Call OpenAI Responses API; try primary model then fallbacks."""
    models = [MODEL] + [m for m in FALLBACK_MODELS if m != MODEL]
    for model in models:
        if model in DISABLED_MODELS:
            continue
        text = call_openai_responses(prompt, model)
        if text is not None:
            return text, model
    return None, None


def call_openai_responses(prompt, model):
    """OpenAI Responses API call. Returns output text or None."""
    url = "https://api.openai.com/v1/responses"
    payload = {
        "model": model,
        "input": prompt,
        "max_output_tokens": MAX_OUTPUT_TOKENS_BY_MODEL.get(model, DEFAULT_MAX_OUTPUT_TOKENS),
        # Enforce valid JSON for easy parsing.
        "text": {"format": JSON_SCHEMA_FORMAT},
    }
    if model in REASONING_EFFORT_BY_MODEL:
        payload["reasoning"] = {"effort": REASONING_EFFORT_BY_MODEL[model]}
    if model not in NO_TEMPERATURE_MODELS:
        payload["temperature"] = 0.2

    req = urllib.request.Request(
        url,
        data=json.dumps(payload).encode(),
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {OPENAI_API_KEY}",
        },
    )

    try:
        timeout = TIMEOUT_BY_MODEL.get(model, DEFAULT_TIMEOUT)
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            result = json.loads(resp.read().decode())
        if result.get("error"):
            log(f"OpenAI error for model={model}: {result['error']}")
            return None
        if result.get("status") and result.get("status") != "completed":
            log(f"OpenAI non-completed status for model={model}: status={result.get('status')} incomplete={result.get('incomplete_details')}")

        chunks = []
        for out in result.get("output", []) or []:
            for c in out.get("content", []) or []:
                if isinstance(c, dict):
                    if "text" in c and isinstance(c["text"], str):
                        chunks.append(c["text"])
                    elif "output_text" in c and isinstance(c["output_text"], str):
                        chunks.append(c["output_text"])
        text = "\n".join(chunks).strip()
        if not text:
            log(f"Empty response text for model={model}")
            return None
        return text
    except urllib.error.HTTPError as e:
        body = ""
        try:
            body = e.read().decode()
        except Exception:
            body = ""
        log(f"OpenAI HTTP {e.code} for model={model}: {body or str(e)}")
        # If model is not available, disable it for the remainder of this run to avoid spam.
        if "model_not_found" in body or "does not exist" in body:
            DISABLED_MODELS.add(model)
        return None
    except Exception as e:
        log(f"OpenAI exception for model={model}: {e}")
        return None

def attempt_proof(filepath, line_num, line_content, full_context, focused_context, agent_id=None):
    """Attempt to prove one sorry with FULL CONTEXT."""
    
    # Truncate full context if needed (keep first 200 + last 100 lines)
    full_lines = full_context.split('\n')
    if len(full_lines) > 400:
        first_part = '\n'.join(full_lines[:200])
        last_part = '\n'.join(full_lines[-100:])
        full_context = first_part + "\n... (middle truncated) ...\n" + last_part
    
    prompt = f"""# CRITICAL: READ ALL CONTEXT BEFORE ATTEMPTING PROOF

{PLACEHOLDER_DEFINITIONS}

{AGENT_CONTEXT_TEXT}

{PROOF_HINTS_TEXT}

---

# YOUR TASK

File: {filepath}
Sorry at Line {line_num}: {line_content}

## FULL FILE CONTENT (understand imports, definitions, structure):
```lean
{full_context}
```

## FOCUSED CONTEXT (around the sorry):
```lean
{focused_context}
```

## DECISION PROCESS

1. Identify the *actual* definitions in scope (SmoothForm is seminormed; Current is `→L[ℝ]`).
2. If you need continuity: use `mkContinuousOfExistsBound` (bounded linear ⇒ continuous) or opNorm bounds.
3. Do NOT assume `smoothExtDeriv` is continuous w.r.t. comass; boundary uses `boundary_bound`.
4. Produce a real Lean proof (no `sorry`, no trivializations).

## Instructions

1. Replace `sorry` with a REAL Lean 4 proof (this agent rejects any patch that still contains `sorry`)
2. NEVER use: `:= trivial`, `:= True`, `True.intro`, `⟨⟩`, or `admit`
3. Prefer: `simp`, `exact`, `apply`, `intro`, `constructor`, `linarith`

## Response Format

Respond with ONLY a JSON object (no markdown, no explanation):
{{"old_code": "the exact line or block containing sorry", "new_code": "the replacement with real proof"}}

Make sure old_code matches exactly what's in the file.
"""
    
    response, used_model = call_openai(prompt)
    if not response:
        return False
    
    try:
        # JSON schema is enforced at the API layer, so this should be valid JSON.
        response = response.strip()
        data = json.loads(response)
        old_code = data.get("old_code", "")
        new_code = data.get("new_code", "")
        
        if not old_code or not new_code:
            log("Empty old/new code")
            return False
        
        if is_trivialization(new_code):
            with stats_lock:
                stats["rejected_trivializations"] += 1
            log(f"REJECTED trivialization", agent_id)
            return False
        
        # Read file and apply change
        full_path = REPO_PATH / filepath
        content = full_path.read_text()
        
        if old_code not in content:
            log(f"Old code not found in file")
            return False
        
        new_content = content.replace(old_code, new_code, 1)
        full_path.write_text(new_content)
        
        # Test build (with lock to prevent concurrent builds)
        module = filepath.replace('/', '.').replace('.lean', '')
        with build_lock:
            ok, output = run_cmd(
                f"export PATH=/home/ubuntu/.elan/bin:$PATH && {LAKE_PATH} build {module} 2>&1 | tail -20",
                timeout=180
            )
        
        if "Build completed" in output or ("error" not in output.lower()):
            if "sorry" in new_code.lower():
                log(f"⚠️  Kept sorry at {filepath}:{line_num} (model={used_model})", agent_id)
                return False
            
            log(f"✅ SUCCESS at {filepath}:{line_num} (model={used_model})", agent_id)
            with stats_lock:
                stats["sorries_eliminated"] += 1
            return True
        else:
            # Revert
            full_path.write_text(content)
            with stats_lock:
                stats["failed_attempts"] += 1
            log(f"Build failed, reverted", agent_id)
            return False
            
    except Exception as e:
        log(f"Error: {e}", agent_id)
        with stats_lock:
            stats["failed_attempts"] += 1
        return False

def agent_worker(agent_id, file_queue):
    """Worker thread for one GPT-5.2 agent."""
    log(f"Starting", agent_id)
    
    with stats_lock:
        stats["agents_active"] += 1
    
    try:
        while True:
            # Get a file to work on
            try:
                filepath = file_queue.get(timeout=10)
            except:
                # Check if more work exists
                for f in TARGET_FILES:
                    if count_sorries(f) > 0:
                        file_queue.put(f)
                continue
            
            # Acquire exclusive lock on this file
            if filepath not in file_locks:
                file_locks[filepath] = threading.Lock()
            
            if not file_locks[filepath].acquire(blocking=False):
                file_queue.put(filepath)  # Put back for another agent
                time.sleep(1)
                continue
            
            try:
                sorry_count = count_sorries(filepath)
                if sorry_count <= 0:
                    continue
                
                log(f"Working on {filepath} ({sorry_count} sorries)", agent_id)
                
                # Work on first sorry - with FULL CONTEXT
                line_num, line_content, full_context, focused_context = find_first_sorry(filepath)
                if line_num:
                    log(f"Attempting line {line_num}...", agent_id)
                    attempt_proof(filepath, line_num, line_content, full_context, focused_context, agent_id)
                
                # Put file back if more sorries remain
                if count_sorries(filepath) > 0:
                    file_queue.put(filepath)
                    
            finally:
                file_locks[filepath].release()
            
            time.sleep(2)  # Rate limiting between attempts
            
    except Exception as e:
        log(f"Worker error: {e}", agent_id)
    finally:
        with stats_lock:
            stats["agents_active"] -= 1
        log(f"Stopping", agent_id)

def main():
    LOG_DIR.mkdir(exist_ok=True)
    
    log("=" * 60)
    log(f"GPT-5.2-HIGH PARALLEL AGENT STARTING ({NUM_AGENTS} agents)")
    log("=" * 60)
    
    stats["start_time"] = time.time()
    
    total = get_total_sorries()
    slack_notify(f"🚀 *GPT-5.2-high Parallel Started*\n• Model: {MODEL}\n• Agents: {NUM_AGENTS}\n• Initial sorries: {total}")
    
    # Create work queue with all files
    file_queue = Queue()
    for f in TARGET_FILES:
        if count_sorries(f) > 0:
            file_queue.put(f)
    
    # Start worker threads
    threads = []
    for i in range(NUM_AGENTS):
        t = threading.Thread(target=agent_worker, args=(i, file_queue), daemon=True)
        t.start()
        threads.append(t)
        time.sleep(0.5)  # Stagger starts
    
    # Monitor progress
    try:
        while True:
            time.sleep(60)
            total = get_total_sorries()
            with stats_lock:
                eliminated = stats["sorries_eliminated"]
                active = stats["agents_active"]
            
            log(f"Status: {eliminated} eliminated, {total} remaining, {active}/{NUM_AGENTS} agents active")
            
            if total == 0:
                slack_notify("🎉 *ALL SORRIES ELIMINATED!*")
                log("🎉 ALL SORRIES ELIMINATED!")
                break
    except KeyboardInterrupt:
        log("Interrupted")
    
    elapsed = (time.time() - stats["start_time"]) / 60
    final_msg = f"""📊 *GPT-5.2-high Agent Complete*
• Elapsed: {elapsed:.1f} min
• Eliminated: {stats['sorries_eliminated']}
• Failed: {stats['failed_attempts']}
• Rejected: {stats['rejected_trivializations']}
• Remaining: {get_total_sorries()}"""
    
    log(final_msg)
    slack_notify(final_msg)

if __name__ == "__main__":
    main()
