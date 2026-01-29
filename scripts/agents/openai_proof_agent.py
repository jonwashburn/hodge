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
from pathlib import Path

# Configuration
OPENAI_API_KEY = os.environ.get("OPENAI_API_KEY", "")
SLACK_WEBHOOK = os.environ.get("SLACK_WEBHOOK", "")
MODEL = os.environ.get("OPENAI_MODEL", "gpt-5.2")
FALLBACK_MODELS = [
    m.strip() for m in os.environ.get("OPENAI_FALLBACK_MODELS", "gpt-5.2-codex,gpt-4o").split(",")
    if m.strip()
]
REPO_PATH = Path("/home/ubuntu/hodge")
LOG_DIR = REPO_PATH / "autonomous_logs"
LAKE_PATH = "/home/ubuntu/.elan/bin/lake"

# Target files with remaining sorries (priority order)
TARGET_FILES = [
    "Hodge/GMT/Mass.lean",           # mass_smul
    "Hodge/GMT/FlatNorm.lean",       # flatNorm theorems
    "Hodge/GMT/Calibration.lean",    # calibration theorems
    "Hodge/Kahler/Main.lean",        # CORE: calibration defect → 0
    "Hodge/Classical/GAGA.lean",     # CORE: fundamental = representing
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

PLACEHOLDER_DEFINITIONS = """
## KEY PLACEHOLDER DEFINITIONS IN THIS CODEBASE

These definitions return trivial values - understand this before proving!

1. comass (Hodge/GMT/Mass.lean:53):
   def comass (_ω : TestForm n X k) : ℝ := 0  -- RETURNS 0!

2. submanifoldIntegral (Hodge/Analytic/Integration/SubmanifoldIntegral.lean:86):
   def submanifoldIntegral (Z : OrientedSubmanifold n X k) (ω : TestForm n X k) : ℂ := 0  -- RETURNS 0!

3. IsSupportedOnAnalyticVariety (Hodge/GMT/Calibration.lean):
   def IsSupportedOnAnalyticVariety (_T : Current n X k) : Prop := True  -- ALWAYS TRUE!

4. isIntegral (Hodge/GMT/FlatNorm.lean):
   isIntegral : Prop := True  -- TRIVIALLY TRUE!

CONSEQUENCE: If a theorem uses comass, RHS of bounds = 0. If it uses submanifoldIntegral, 
currents evaluate to 0. Some theorems become unprovable as stated - use sorry with docs.
"""

def load_agent_context():
    try:
        return AGENT_CONTEXT_PATH.read_text()
    except Exception:
        return ""

AGENT_CONTEXT_TEXT = load_agent_context()

PROOF_HINTS = """
## Key Proof Patterns That Work:

### 1. Triangle Inequality for iSup (mass_add pattern):
```lean
apply iSup₂_le
intro ω hω
have h1 : (‖(S + T) ω‖₊ : ℝ≥0∞) ≤ ‖S ω‖₊ + ‖T ω‖₊ := by
  have : (S + T) ω = S ω + T ω := LinearMap.add_apply S T ω
  rw [this]
  exact_mod_cast nnnorm_add_le (S ω) (T ω)
have h2 : (‖S ω‖₊ : ℝ≥0∞) ≤ ⨆ ω' ∈ comassUnitBall n X k, (‖S ω'‖₊ : ℝ≥0∞) := by
  apply le_iSup₂_of_le ω hω
  rfl
-- ... combine with add_le_add h2 h3
```

### 2. Infimum Upper Bound (flatNorm_le_mass pattern):
```lean
have h : T = T + Current.boundary 0 := by simp [Current.boundary]
apply iInf_le_of_le T
apply iInf_le_of_le 0
apply iInf_le_of_le h
```

### 3. Key Lemmas:
- `LinearMap.add_apply`: `(S + T) ω = S ω + T ω`
- `LinearMap.smul_apply`: `(c • T) ω = c • T ω`
- `nnnorm_add_le`: triangle inequality for nnnorm
- `nnnorm_smul`: `‖c • x‖₊ = ‖c‖₊ * ‖x‖₊`
- `le_iSup₂_of_le`: prove ≤ iSup by exhibiting witness
- `iSup₂_le`: prove iSup ≤ something by proving for all elements
- `iInf_le_of_le`: prove iInf ≤ something by exhibiting witness
- `ENNReal.mul_iSup`: factor out multiplication from iSup
- `mass_zero`: `mass 0 = 0`
- `mass_add`: already proven, use it!

### 4. Specific Hints:
- mass_smul: Use `LinearMap.smul_apply`, `nnnorm_smul`, then factor ‖c‖₊ using ENNReal.mul_iSup
- flatNorm_add: Decompose S = R₁ + ∂S₁, T = R₂ + ∂S₂, then S+T = (R₁+R₂) + ∂(S₁+S₂)
- flatNormTopology: Use `UniformSpace.toTopologicalSpace` with flat norm metric
"""

stats = {
    "start_time": None,
    "sorries_eliminated": 0,
    "failed_attempts": 0,
    "rejected_trivializations": 0,
}

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

def log(msg):
    ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    line = f"[{ts}] [OpenAI] {msg}"
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

def attempt_proof(filepath, line_num, line_content, full_context, focused_context):
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

{PROOF_HINTS}

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

1. Does this theorem use `comass`? → RHS of bounds = 0 (placeholder)
2. Does this theorem use `submanifoldIntegral`? → Currents evaluate to 0
3. Is this a "deep content" sorry? → May need to remain as documented sorry
4. Can this actually be proven given the placeholder definitions?

## Instructions

1. If provable: Replace `sorry` with a REAL Lean 4 proof
2. If deep content: Leave as sorry but document WHY
3. NEVER use: `:= trivial`, `:= True`, `True.intro`, `⟨⟩`, or `admit`
4. Use proper tactics: `simp`, `exact`, `apply`, `intro`, `constructor`, `linarith`

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
            stats["rejected_trivializations"] += 1
            log(f"REJECTED trivialization")
            return False
        
        # Read file and apply change
        full_path = REPO_PATH / filepath
        content = full_path.read_text()
        
        if old_code not in content:
            log(f"Old code not found in file")
            return False
        
        new_content = content.replace(old_code, new_code, 1)
        full_path.write_text(new_content)
        
        # Test build
        module = filepath.replace('/', '.').replace('.lean', '')
        ok, output = run_cmd(
            f"export PATH=/home/ubuntu/.elan/bin:$PATH && {LAKE_PATH} build {module} 2>&1 | tail -20",
            timeout=180
        )
        
        if "Build completed" in output or ("error" not in output.lower()):
            log(f"✅ SUCCESS at {filepath}:{line_num} (model={used_model})")
            stats["sorries_eliminated"] += 1
            return True
        else:
            # Revert
            full_path.write_text(content)
            stats["failed_attempts"] += 1
            log(f"Build failed, reverted")
            return False
            
    except Exception as e:
        log(f"Error: {e}")
        stats["failed_attempts"] += 1
        return False

def main():
    LOG_DIR.mkdir(exist_ok=True)
    
    log("=" * 60)
    log(f"GPT-5.2-HIGH PROOF AGENT STARTING")
    log("=" * 60)
    
    stats["start_time"] = time.time()
    
    total = get_total_sorries()
    slack_notify(f"🚀 *GPT-5.2-high Agent Started*\n• Model: {MODEL}\n• Target files: {len(TARGET_FILES)}\n• Initial sorries: {total}")
    
    cycles = 0
    while True:
        cycles += 1
        log(f"\n=== CYCLE {cycles} ===")
        
        total = get_total_sorries()
        if total == 0:
            slack_notify("🎉 *ALL SORRIES ELIMINATED!*")
            log("🎉 ALL SORRIES ELIMINATED!")
            break
        
        log(f"Remaining sorries: {total}")
        
        for filepath in TARGET_FILES:
            sorry_count = count_sorries(filepath)
            if sorry_count <= 0:
                continue
            
            log(f"\n--- {filepath}: {sorry_count} sorries ---")
            
            # Now with FULL FILE CONTEXT
            line_num, line_content, full_context, focused_context = find_first_sorry(filepath)
            if line_num is None:
                continue
            
            log(f"Attempting line {line_num}...")
            attempt_proof(filepath, line_num, line_content, full_context, focused_context)
            
            time.sleep(2)  # Rate limiting
        
        time.sleep(5)
    
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
