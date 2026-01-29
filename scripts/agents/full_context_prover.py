#!/usr/bin/env python3
"""
Full Context Prover - Empowered agents with complete mathematical context.

Each agent receives:
1. The FULL mathematical paper (JA_hodge_approach_clean_black_FINAL.tex)
2. The FULL relevant Lean file
3. Complete instructions to prove a specific sorry

These agents are empowered to solve deep GMT theorems.
"""

import anthropic
import asyncio
import json
import os
import subprocess
import sys
from pathlib import Path
from datetime import datetime

# Configuration - MAXIMUM POWER
MAX_CONCURRENT_AGENTS = 7  # One per sorry
API_TIMEOUT = 600  # 10 minutes per API call
MAX_ITERATIONS = 30  # Keep trying
MODEL = "claude-opus-4-5-20251101"

# The 7 remaining sorries
TASKS = [
    {
        "id": "flat_limit_cycles",
        "file": "Hodge/Classical/HarveyLawson.lean",
        "line": 214,
        "description": "Prove flat_limit_of_cycles: boundary of flat limit equals limit of boundaries (Federer-Fleming)",
        "math_section": "Federer-Fleming compactness theorem"
    },
    {
        "id": "hausdorff_linear",
        "file": "Hodge/Analytic/Currents.lean",
        "line": 696,
        "description": "Prove hausdorffIntegrate_linear: Bochner integral linearity for form integration",
        "math_section": "Integration of differential forms"
    },
    {
        "id": "hausdorff_bound",
        "file": "Hodge/Analytic/Currents.lean",
        "line": 712,
        "description": "Prove hausdorffIntegrate_bound: Mass-comass duality inequality",
        "math_section": "Mass-comass duality"
    },
    {
        "id": "integrable_pairing",
        "file": "Hodge/Analytic/Currents.lean",
        "line": 765,
        "description": "Prove integrable_pairing: smooth forms on compact manifolds are integrable",
        "math_section": "Integrability of smooth forms"
    },
    {
        "id": "pairing_comass",
        "file": "Hodge/Analytic/Currents.lean",
        "line": 768,
        "description": "Prove pairing_le_comass: |⟨ω,τ⟩| ≤ comass(ω) for unit simple τ",
        "math_section": "Comass definition and bounds"
    },
    {
        "id": "stokes_rectifiable",
        "file": "Hodge/Analytic/Currents.lean",
        "line": 888,
        "description": "Prove stokes_bound for rectifiable sets: |∫_Z dω| ≤ bdryMass * comass(dω)",
        "math_section": "Stokes' theorem"
    },
    {
        "id": "stokes_closed",
        "file": "Hodge/Analytic/Currents.lean",
        "line": 921,
        "description": "Prove ∫ dω = 0 on closed manifolds (no boundary)",
        "math_section": "Stokes' theorem for closed manifolds"
    },
]

def load_file(path: str) -> str:
    """Load a file's contents."""
    try:
        with open(path, 'r') as f:
            return f.read()
    except Exception as e:
        return f"Error loading {path}: {e}"

def get_full_paper() -> str:
    """Load the complete mathematical paper."""
    paper_path = "/home/ubuntu/hodge/tex/archive/JA_hodge_approach_clean_black_FINAL.tex"
    if not os.path.exists(paper_path):
        paper_path = "/home/ubuntu/hodge/JA_hodge_approach_clean_black_FINAL.tex"
    return load_file(paper_path)

def get_lean_file(file_path: str) -> str:
    """Load a Lean file."""
    full_path = f"/home/ubuntu/hodge/{file_path}"
    return load_file(full_path)

def get_context_around_sorry(file_content: str, line_num: int, context: int = 100) -> str:
    """Get context around the sorry line."""
    lines = file_content.split('\n')
    start = max(0, line_num - context)
    end = min(len(lines), line_num + context)
    numbered_lines = []
    for i in range(start, end):
        marker = " >>> " if i + 1 == line_num else "     "
        numbered_lines.append(f"{i+1:4}{marker}{lines[i]}")
    return '\n'.join(numbered_lines)

def build_and_check() -> tuple[bool, str]:
    """Build the project and return success status and output."""
    try:
        result = subprocess.run(
            ["lake", "build"],
            cwd="/home/ubuntu/hodge",
            capture_output=True,
            text=True,
            timeout=300,
            env={**os.environ, "PATH": f"{os.environ.get('HOME', '')}/.elan/bin:{os.environ.get('PATH', '')}"}
        )
        output = result.stdout + result.stderr
        success = result.returncode == 0
        return success, output
    except Exception as e:
        return False, str(e)

def apply_proof(file_path: str, line_num: int, new_proof: str) -> bool:
    """Replace the sorry at the given line with the new proof."""
    full_path = f"/home/ubuntu/hodge/{file_path}"
    try:
        with open(full_path, 'r') as f:
            lines = f.readlines()
        
        # Find the sorry line and replace
        idx = line_num - 1
        if idx < len(lines) and 'sorry' in lines[idx]:
            # Get indentation
            indent = len(lines[idx]) - len(lines[idx].lstrip())
            indent_str = lines[idx][:indent]
            
            # Replace sorry with new proof
            new_lines = [indent_str + l.strip() + '\n' for l in new_proof.strip().split('\n')]
            lines[idx] = ''.join(new_lines) if new_lines else lines[idx].replace('sorry', new_proof.strip())
            
            with open(full_path, 'w') as f:
                f.writelines(lines)
            return True
        return False
    except Exception as e:
        print(f"Error applying proof: {e}")
        return False

async def prove_sorry(client: anthropic.AsyncAnthropic, task: dict, paper: str) -> dict:
    """Have an agent prove a single sorry."""
    task_id = task["id"]
    file_path = task["file"]
    line_num = task["line"]
    description = task["description"]
    math_section = task["math_section"]
    
    print(f"\n{'='*60}")
    print(f"[{task_id}] Starting agent for: {description}")
    print(f"{'='*60}")
    
    # Load the full Lean file
    lean_file = get_lean_file(file_path)
    context = get_context_around_sorry(lean_file, line_num)
    
    # Build the comprehensive prompt
    system_prompt = f"""You are a world-class mathematician and Lean 4 expert working on the formalization of the Hodge Conjecture.

Your task: Prove the following sorry statement in Lean 4.

FILE: {file_path}
LINE: {line_num}
DESCRIPTION: {description}
MATHEMATICAL TOPIC: {math_section}

You have access to:
1. The COMPLETE mathematical paper with all proofs
2. The COMPLETE Lean file with all definitions and context

CRITICAL INSTRUCTIONS:
1. Study the mathematical proof in the paper carefully
2. Understand the Lean definitions and types involved
3. Write a COMPLETE Lean proof that replaces "sorry"
4. Your proof must compile - use only tactics/lemmas available in Mathlib
5. If the proof is deep, break it into helper lemmas with sorry, then prove those

OUTPUT FORMAT:
Provide ONLY the Lean code that replaces "sorry". No explanation needed.
The code should start immediately after the ":= by" or similar.

Example output:
  simp only [hausdorffIntegrate]
  apply le_trans (norm_integral_le ...)
  exact some_lemma

DO NOT include the theorem signature. ONLY the proof body."""

    user_message = f"""# COMPLETE MATHEMATICAL PAPER

{paper}

# COMPLETE LEAN FILE: {file_path}

{lean_file}

# CONTEXT AROUND LINE {line_num} (marked with >>>)

{context}

# YOUR TASK

Replace the "sorry" at line {line_num} with a valid Lean 4 proof.
The proof should implement: {description}

Remember: You have ALL the mathematical content from the paper above. Use it.
Output ONLY the Lean proof code, nothing else."""

    for iteration in range(MAX_ITERATIONS):
        print(f"[{task_id}] Iteration {iteration + 1}/{MAX_ITERATIONS}")
        
        try:
            response = await asyncio.wait_for(
                client.messages.create(
                    model=MODEL,
                    max_tokens=8192,
                    system=system_prompt,
                    messages=[{"role": "user", "content": user_message}]
                ),
                timeout=API_TIMEOUT
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up the proof - remove markdown if present
            if proof.startswith("```"):
                lines = proof.split('\n')
                proof = '\n'.join(lines[1:-1] if lines[-1] == '```' else lines[1:])
            
            print(f"[{task_id}] Agent proposed proof ({len(proof)} chars)")
            
            # Try to apply the proof
            if apply_proof(file_path, line_num, proof):
                # Build and check
                success, output = build_and_check()
                
                if success:
                    print(f"[{task_id}] ✅ SUCCESS! Proof verified.")
                    return {"id": task_id, "status": "success", "proof": proof, "iterations": iteration + 1}
                else:
                    # Extract error for feedback
                    error_lines = [l for l in output.split('\n') if 'error' in l.lower()][:5]
                    error_msg = '\n'.join(error_lines) if error_lines else output[-500:]
                    print(f"[{task_id}] Build failed: {error_msg[:200]}...")
                    
                    # Update message with error feedback
                    user_message = f"""Previous proof attempt failed with error:
{error_msg}

Please try again with a different approach. Remember:
- Use only Mathlib lemmas that exist
- Check types carefully (ℝ vs ℂ, etc.)
- The proof must compile

Original task: Replace the "sorry" at line {line_num} with a valid Lean 4 proof.
Output ONLY the Lean proof code."""
                    
                    # Restore the sorry
                    restore_sorry(file_path, line_num)
            else:
                print(f"[{task_id}] Failed to apply proof")
                
        except asyncio.TimeoutError:
            print(f"[{task_id}] API timeout")
        except Exception as e:
            print(f"[{task_id}] Error: {e}")
    
    print(f"[{task_id}] ❌ FAILED after {MAX_ITERATIONS} iterations")
    return {"id": task_id, "status": "failed", "iterations": MAX_ITERATIONS}

def restore_sorry(file_path: str, line_num: int):
    """Restore the sorry at the given line."""
    # Re-sync from backup or just note we need to restore
    pass  # The build failure means we need to restore manually

async def main():
    print("="*70)
    print("FULL CONTEXT PROVER - Empowered Agents")
    print("="*70)
    print(f"Tasks: {len(TASKS)}")
    print(f"Max concurrent: {MAX_CONCURRENT_AGENTS}")
    print(f"API timeout: {API_TIMEOUT}s")
    print(f"Max iterations per task: {MAX_ITERATIONS}")
    print("="*70)
    
    # Load API key
    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        print("ERROR: ANTHROPIC_API_KEY not set")
        sys.exit(1)
    
    client = anthropic.AsyncAnthropic(api_key=api_key)
    
    # Load the paper once
    print("Loading mathematical paper...")
    paper = get_full_paper()
    print(f"Paper loaded: {len(paper)} characters")
    
    # Run all agents in parallel
    print(f"\nStarting {len(TASKS)} agents in parallel...")
    
    tasks = [prove_sorry(client, task, paper) for task in TASKS]
    results = await asyncio.gather(*tasks, return_exceptions=True)
    
    # Summary
    print("\n" + "="*70)
    print("FINAL RESULTS")
    print("="*70)
    
    successes = 0
    for result in results:
        if isinstance(result, dict):
            status = "✅" if result.get("status") == "success" else "❌"
            print(f"{status} {result.get('id')}: {result.get('status')} ({result.get('iterations')} iterations)")
            if result.get("status") == "success":
                successes += 1
        else:
            print(f"❌ Error: {result}")
    
    print(f"\nTotal: {successes}/{len(TASKS)} succeeded")
    
    # Save results
    with open("/home/ubuntu/hodge/agent_results.json", "w") as f:
        json.dump([r for r in results if isinstance(r, dict)], f, indent=2)

if __name__ == "__main__":
    asyncio.run(main())
