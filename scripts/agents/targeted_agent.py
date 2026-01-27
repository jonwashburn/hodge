#!/usr/bin/env python3
"""
Targeted Agent - Gives specific hints for each sorry.

Each sorry gets domain-specific guidance about which Mathlib lemmas to use.
"""

import anthropic
import asyncio
import os
import subprocess
import shutil

BASE_DIR = "/home/ubuntu/hodge"
BACKUP_DIR = "/home/ubuntu/hodge_backup"
API_TIMEOUT = 300
MAX_ITERATIONS = 10
MODEL = "claude-sonnet-4-20250514"

# Specific hints for each sorry - UPDATED with correct Mathlib names
SORRY_HINTS = {
    "Hodge/Analytic/Currents.lean:697": {
        "name": "hausdorffIntegrate_linear",
        "goal": "hausdorffIntegrate data (c • ω₁ + ω₂) = c * hausdorffIntegrate data ω₁ + hausdorffIntegrate data ω₂",
        "hints": """
This is integral linearity. Key Mathlib lemmas:
- MeasureTheory.integral_add : ∫ (f + g) = ∫ f + ∫ g 
- MeasureTheory.integral_smul : ∫ (c • f) = c • ∫ f

The definition is: hausdorffIntegrate data ω = (∫ x in data.carrier, formVectorPairing ω data.orientation x ∂data.measure).re

Try:
  simp only [hausdorffIntegrate]
  -- then use integral_add, integral_smul
  -- then simp Complex.add_re, Complex.smul_re
"""
    },
    "Hodge/Analytic/Currents.lean:714": {
        "name": "hausdorffIntegrate_bound",
        "goal": "|hausdorffIntegrate data ω| ≤ data.mass * comass ω",
        "hints": """
Mass-comass duality. Key Mathlib lemmas:
- MeasureTheory.norm_integral_le_integral_norm
- Complex.abs_re_le_norm : |z.re| ≤ ‖z‖

Try using calc:
  calc |hausdorffIntegrate data ω| 
    ≤ ‖∫ ...‖ := Complex.abs_re_le_norm _
    ≤ ∫ ‖...‖ := MeasureTheory.norm_integral_le_integral_norm _
    ...
"""
    },
    "Hodge/Analytic/Currents.lean:769": {
        "name": "integrable_pairing",
        "goal": "Integrable (fun x => formVectorPairing ω data.orientation x) data.measure",
        "hints": """
Integrability of bounded function on finite measure. Use:
- MeasureTheory.Integrable.of_bound [IsFiniteMeasure μ] 
  (hf : AEStronglyMeasurable f μ) (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C)

Need to show:
1. AEStronglyMeasurable (smooth => continuous => measurable)
2. Bounded by comass

Try: sorry (this is a deep result about smooth forms)
"""
    },
    "Hodge/Analytic/Currents.lean:772": {
        "name": "pairing_le_comass", 
        "goal": "‖formVectorPairing ω data.orientation x‖ ≤ comass ω",
        "hints": """
This follows from comass definition: comass = sup |⟨ω,v⟩| over unit simple vectors.
If orientation is unit simple, the bound holds by definition.

Try: sorry (needs comass definition infrastructure)
"""
    },
    "Hodge/Analytic/Currents.lean:892": {
        "name": "stokes_bound (rectifiable)",
        "goal": "|∫_Z dω| ≤ bdryMass * comass(dω)",
        "hints": """
Stokes theorem: ∫_Z dω = ∫_∂Z ω.
Then apply hausdorffIntegrate_bound to boundary.

Try: sorry (needs Stokes theorem formalized)
"""
    },
    "Hodge/Analytic/Currents.lean:925": {
        "name": "stokes_bound (closed)",
        "goal": "hausdorffIntegrate data.toOrientedData (smoothExtDeriv ω) = 0",
        "hints": """
For closed manifolds (no boundary): ∫_Z dω = ∫_∂Z ω = 0.
The boundary is empty, so integral over empty set is 0.

Try: sorry (needs Stokes theorem for closed manifolds)
"""
    },
    "Hodge/Classical/HarveyLawson.lean:220": {
        "name": "flat_limit_of_cycles",
        "goal": "flatNorm (Current.boundary T_limit.toFun) = 0",
        "hints": """
Key lemmas available:
- flatNorm_boundary_le : flatNorm (∂T) ≤ flatNorm T
- flatNorm_eq_zero_iff : flatNorm T = 0 ↔ T = 0

Strategy:
1. h_cycles says each T_seq i is a cycle, so ∂(T_seq i) = 0
2. h_conv says flatNorm (T_seq i - T_limit) → 0
3. flatNorm (∂T_limit) ≤ flatNorm (T_limit - T_seq i) → 0 by flatNorm_boundary_le
4. So flatNorm (∂T_limit) = 0

Try proving the convergence argument with Filter.Tendsto lemmas.
"""
    }
}

def run_cmd(cmd, cwd=None, timeout=300):
    env = os.environ.copy()
    env["PATH"] = f"{os.environ.get('HOME', '')}/.elan/bin:{env.get('PATH', '')}"
    try:
        result = subprocess.run(
            cmd, shell=True, cwd=cwd or BASE_DIR,
            capture_output=True, text=True, timeout=timeout, env=env
        )
        return result.returncode == 0, result.stdout + result.stderr
    except Exception as e:
        return False, str(e)

def create_backup():
    if os.path.exists(BACKUP_DIR):
        shutil.rmtree(BACKUP_DIR)
    shutil.copytree(f"{BASE_DIR}/Hodge", BACKUP_DIR)

def restore_backup():
    if os.path.exists(BACKUP_DIR):
        shutil.rmtree(f"{BASE_DIR}/Hodge")
        shutil.copytree(BACKUP_DIR, f"{BASE_DIR}/Hodge")

def load_file(path):
    with open(f"{BASE_DIR}/{path}", 'r') as f:
        return f.read()

def save_file(path, content):
    with open(f"{BASE_DIR}/{path}", 'w') as f:
        f.write(content)

def replace_sorry(file_path, line_num, proof):
    content = load_file(file_path)
    lines = content.split('\n')
    old_line = lines[line_num - 1]
    indent = len(old_line) - len(old_line.lstrip())
    proof_lines = proof.strip().split('\n')
    new_content = '\n'.join(' ' * indent + l.strip() for l in proof_lines)
    lines[line_num - 1] = new_content
    save_file(file_path, '\n'.join(lines))

async def prove_sorry(client, file_path, line_num):
    key = f"{file_path}:{line_num}"
    hints = SORRY_HINTS.get(key, {"name": "unknown", "goal": "unknown", "hints": ""})
    
    print(f"\n{'='*60}")
    print(f"TARGET: {key} ({hints['name']})")
    print(f"{'='*60}")
    
    create_backup()
    
    lean_file = load_file(file_path)
    lines = lean_file.split('\n')
    context = '\n'.join(f"{i+1}: {lines[i]}" for i in range(max(0, line_num-30), min(len(lines), line_num+10)))
    
    system = f"""You are a Lean 4 + Mathlib expert. Prove this sorry.

GOAL: {hints['goal']}

SPECIFIC HINTS:
{hints['hints']}

OUTPUT: Only the Lean proof code that replaces sorry. No explanation."""

    user = f"""FILE: {file_path}
LINE: {line_num}

CONTEXT:
{context}

Write ONLY the Lean 4 proof code."""

    for i in range(MAX_ITERATIONS):
        print(f"  Attempt {i+1}/{MAX_ITERATIONS}")
        try:
            response = await asyncio.wait_for(
                client.messages.create(
                    model=MODEL,
                    max_tokens=1024,
                    system=system,
                    messages=[{"role": "user", "content": user}]
                ),
                timeout=API_TIMEOUT
            )
            
            proof = response.content[0].text.strip()
            if "```" in proof:
                lines = proof.split('\n')
                proof = '\n'.join(l for l in lines if not l.startswith('```'))
            
            print(f"  Proof: {proof[:60]}...")
            
            replace_sorry(file_path, line_num, proof)
            success, output = run_cmd("lake build")
            
            if success:
                print(f"  ✅ SUCCESS!")
                create_backup()
                return True
            else:
                errors = [l for l in output.split('\n') if 'error' in l.lower()][:3]
                print(f"  Failed: {errors[0] if errors else 'unknown'}")
                restore_backup()
                user = f"Previous failed with: {errors}. Try different approach."
                
        except Exception as e:
            print(f"  Error: {e}")
            restore_backup()
    
    print(f"  ❌ Failed")
    restore_backup()
    return False

async def main():
    print("TARGETED AGENT")
    
    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        print("No API key")
        return
    
    client = anthropic.AsyncAnthropic(api_key=api_key)
    
    # Verify build
    success, _ = run_cmd("lake build")
    if not success:
        print("Build not clean!")
        return
    
    create_backup()
    
    # Find sorries
    _, output = run_cmd("grep -rn '^\\s*sorry' Hodge/ --include='*.lean'")
    sorries = []
    for line in output.strip().split('\n'):
        if ':' in line:
            parts = line.split(':')
            sorries.append((parts[0], int(parts[1])))
    
    print(f"Found {len(sorries)} sorries")
    
    successes = 0
    for file_path, line_num in sorries:
        if await prove_sorry(client, file_path, line_num):
            successes += 1
    
    print(f"\nFINAL: {successes}/{len(sorries)} eliminated")

if __name__ == "__main__":
    asyncio.run(main())
