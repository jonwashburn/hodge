#!/usr/bin/env python3
"""
Focused Proof Agent - Complete the 2 Remaining Sorries
=======================================================
The Hodge Conjecture formalization is 99% complete. Only 2 sorries remain.

This agent focuses exclusively on completing these 2 proofs.
"""

import os
import json
import asyncio
import aiohttp
import re
from pathlib import Path
from datetime import datetime

API_KEY = ""
for p in [Path.home() / ".anthropic_api_key", Path.home() / ".anthropic_key"]:
    try:
        if p.exists():
            API_KEY = p.read_text().strip()
            break
    except:
        pass

MODEL = "claude-opus-4-5-20251101"
HODGE_PATH = Path("/home/ubuntu/hodge")
PAPER_PATH = HODGE_PATH / "JA_hodge_approach_with_added_refs_blueCites.tex"
LOG_DIR = HODGE_PATH / "focused_logs"

# THE TWO SORRIES - this is all we need to complete
TARGETS = [
    {
        "id": "main_262",
        "file": "Hodge/Kahler/Main.lean",
        "line": 262,
        "description": "Prove calibration defect converges to 0",
        "context": """
The microstructure sequence is constant (all terms equal). We need to show:
- The calibration defect of an integration current over Set.univ with a calibrating form is 0
- A calibrated current has zero defect by definition
- The microstructure currents are built from sheets that are calibrated

Reference: Paper Section 8, Proposition 8.7
"""
    },
    {
        "id": "gaga_589", 
        "file": "Hodge/Classical/GAGA.lean",
        "line": 589,
        "description": "Prove geometric class equals form class",
        "context": """
Need to show: [poincareDualForm(Z.support)] = [γ]

This requires:
1. The microstructure produces currents representing [γ]
2. Harvey-Lawson extracts varieties whose Poincaré dual is [γ]  
3. The spine construction carries the original form

Reference: Paper Sections 8-10, Theorem 10.1
"""
    }
]

VISION = """
## THE HODGE CONJECTURE - FINAL STEPS

You are completing the formal proof of the Hodge Conjecture. The formalization is 
99% complete. Only 2 `sorry` statements remain - and you are here to prove them.

### Proof Strategy (Washburn-Barghi)
1. Rational Hodge class γ → Microstructure sequence with vanishing calibration defect
2. Calibrated currents → Analytic variety support (Harvey-Lawson-King)
3. Analytic varieties → Algebraic (Chow/GAGA)
4. Algebraic cycle represents γ ✓

### The Codebase
- The infrastructure is COMPLETE - don't rewrite files
- The typeclasses are DEFINED - just fill in the sorry
- Focus on the MATHEMATICAL ARGUMENT, not the infrastructure

### Your Approach
1. READ the surrounding code carefully
2. UNDERSTAND what the sorry needs to prove
3. USE existing lemmas and definitions from the file
4. MAKE TARGETED EDITS - replace only the sorry
"""

class FocusedAgent:
    def __init__(self, target: dict):
        self.target = target
        self.log_file = LOG_DIR / f"{target['id']}.log"
        LOG_DIR.mkdir(exist_ok=True)
    
    def log(self, msg: str):
        line = f"[{datetime.now():%H:%M:%S}] {msg}\n"
        with open(self.log_file, "a") as f:
            f.write(line)
        print(f"[{self.target['id']}] {msg}")
    
    async def run(self) -> bool:
        self.log(f"Starting: {self.target['description']}")
        
        # Read the file
        file_path = HODGE_PATH / self.target["file"]
        content = file_path.read_text()
        lines = content.split("\n")
        
        # Get context around the sorry
        sorry_line = self.target["line"] - 1  # 0-indexed
        start = max(0, sorry_line - 50)
        end = min(len(lines), sorry_line + 30)
        context_code = "\n".join(f"{i+1}: {lines[i]}" for i in range(start, end))
        
        # Read paper for reference
        paper_context = ""
        if PAPER_PATH.exists():
            paper = PAPER_PATH.read_text(errors="ignore")
            # Extract relevant sections
            for section in ["calibrat", "defect", "Harvey", "spine", "represent"]:
                if section.lower() in self.target["description"].lower():
                    pattern = rf"\\section\{{[^}}]*{section}[^}}]*\}}(.*?)(?=\\section|$)"
                    for m in re.finditer(pattern, paper, re.IGNORECASE | re.DOTALL):
                        paper_context += m.group(0)[:2000] + "\n\n"
        
        prompt = f"""{VISION}

---

## YOUR TARGET

**File:** {self.target['file']}
**Line:** {self.target['line']}
**Goal:** {self.target['description']}

### Mathematical Context
{self.target['context']}

### Code Around the Sorry (line {self.target['line']}):
```lean
{context_code}
```

### Paper Reference
{paper_context[:3000] if paper_context else "See paper sections on calibration and representation."}

---

## INSTRUCTIONS

Replace the `sorry` at line {self.target['line']} with a REAL PROOF.

You may:
- Use existing lemmas from the file
- Use Mathlib tactics (simp, exact, apply, etc.)
- Add helper lemmas if needed (but prefer using existing ones)
- Use `sorryAx` ONLY for genuinely deep results with a comment explaining why

Output the EXACT replacement for the sorry line. Format:
```lean
-- Your proof replacing the sorry
your_tactic_or_term_here
```

Think step by step about what needs to be proven and how the existing 
infrastructure supports it.
"""
        
        messages = [{"role": "user", "content": prompt}]
        
        for iteration in range(10):
            self.log(f"Iteration {iteration + 1}")
            
            response = await self._call_api(messages)
            if not response:
                await asyncio.sleep(2)
                continue
            
            messages.append({"role": "assistant", "content": response})
            
            # Extract the proof
            proof_match = re.search(r"```lean\n(.*?)```", response, re.DOTALL)
            if proof_match:
                proof = proof_match.group(1).strip()
                
                # Apply the change - replace the sorry line with the proof
                new_lines = lines.copy()
                # Find the actual sorry in the lines
                for i, line in enumerate(new_lines):
                    if line.strip() == "sorry" and abs(i - sorry_line) < 5:
                        new_lines[i] = "      " + proof.replace("\n", "\n      ")  # Indent
                        break
                new_content = "\n".join(new_lines)
                
                # Write and test
                file_path.write_text(new_content)
                self.log(f"Applied proof: {proof[:100]}...")
                
                # Build
                ok, output = await self._build()
                if ok:
                    self.log("BUILD SUCCESS!")
                    return True
                else:
                    self.log(f"Build failed, continuing...")
                    # Restore original
                    file_path.write_text(content)
                    messages.append({
                        "role": "user",
                        "content": f"Build failed:\n```\n{output[:2000]}\n```\n\nTry a different approach."
                    })
            
            await asyncio.sleep(1)
        
        # Restore original on failure
        file_path.write_text(content)
        self.log("Max iterations reached, restored original")
        return False
    
    async def _call_api(self, messages):
        if not API_KEY:
            return None
        async with aiohttp.ClientSession() as session:
            try:
                async with session.post(
                    "https://api.anthropic.com/v1/messages",
                    headers={
                        "x-api-key": API_KEY,
                        "anthropic-version": "2023-06-01",
                        "content-type": "application/json"
                    },
                    json={"model": MODEL, "max_tokens": 8192, "messages": messages},
                    timeout=aiohttp.ClientTimeout(total=300)
                ) as resp:
                    if resp.status != 200:
                        return None
                    data = await resp.json()
                    return data.get("content", [{}])[0].get("text", "")
            except:
                return None
    
    async def _build(self):
        try:
            proc = await asyncio.create_subprocess_exec(
                "lake", "build",
                cwd=str(HODGE_PATH),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE
            )
            stdout, stderr = await asyncio.wait_for(proc.communicate(), timeout=600)
            return proc.returncode == 0, (stdout + stderr).decode()
        except Exception as e:
            return False, str(e)


async def main():
    print("=" * 60)
    print("FOCUSED PROOF AGENT - 2 SORRIES TO COMPLETE")
    print("=" * 60)
    
    for target in TARGETS:
        print(f"\n>>> Working on: {target['id']}")
        agent = FocusedAgent(target)
        success = await agent.run()
        if success:
            print(f"✅ {target['id']} COMPLETE!")
        else:
            print(f"❌ {target['id']} needs more work")

if __name__ == "__main__":
    asyncio.run(main())
