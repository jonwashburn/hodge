#!/usr/bin/env python3
"""
Sequential Prover - One agent at a time, with full context and careful file handling.

Each agent receives:
1. The FULL mathematical paper
2. The FULL relevant Lean file
3. Complete instructions to prove a specific sorry

After each success, we commit and move to the next.
"""

import anthropic
import asyncio
import json
import os
import subprocess
import sys
import shutil
from pathlib import Path
from datetime import datetime

# Configuration
API_TIMEOUT = 600  # 10 minutes
MAX_ITERATIONS = 20
MODEL = "claude-sonnet-4-20250514"

BASE_DIR = "/home/ubuntu/hodge"

# The 7 remaining sorries - will be updated dynamically
def get_remaining_sorries():
    """Dynamically find remaining sorries."""
    result = subprocess.run(
        ["grep", "-rn", "^\\s*sorry", "Hodge/", "--include=*.lean"],
        cwd=BASE_DIR,
        capture_output=True,
        text=True
    )
    sorries = []
    for line in result.stdout.strip().split('\n'):
        if line and ':' in line:
            parts = line.split(':')
            if len(parts) >= 2:
                file_path = parts[0]
                line_num = int(parts[1])
                sorries.append({"file": file_path, "line": line_num})
    return sorries

def load_file(path: str) -> str:
    """Load a file's contents."""
    full_path = os.path.join(BASE_DIR, path) if not path.startswith('/') else path
    try:
        with open(full_path, 'r') as f:
            return f.read()
    except Exception as e:
        return f"Error loading {path}: {e}"

def save_file(path: str, content: str):
    """Save content to a file."""
    full_path = os.path.join(BASE_DIR, path) if not path.startswith('/') else path
    with open(full_path, 'w') as f:
        f.write(content)

def backup_file(path: str) -> str:
    """Create a backup of a file."""
    full_path = os.path.join(BASE_DIR, path)
    backup_path = full_path + ".backup"
    shutil.copy2(full_path, backup_path)
    return backup_path

def restore_file(path: str):
    """Restore a file from backup."""
    full_path = os.path.join(BASE_DIR, path)
    backup_path = full_path + ".backup"
    if os.path.exists(backup_path):
        shutil.copy2(backup_path, full_path)

def get_full_paper() -> str:
    """Load the complete mathematical paper."""
    paths = [
        "tex/archive/JA_hodge_approach_clean_black_FINAL.tex",
        "JA_hodge_approach_clean_black_FINAL.tex"
    ]
    for p in paths:
        content = load_file(p)
        if not content.startswith("Error"):
            return content
    return "Paper not found"

def get_surrounding_context(file_path: str, line_num: int, before: int = 50, after: int = 20) -> str:
    """Get lines around the sorry."""
    content = load_file(file_path)
    lines = content.split('\n')
    start = max(0, line_num - before - 1)
    end = min(len(lines), line_num + after)
    
    result = []
    for i in range(start, end):
        marker = ">>> " if i == line_num - 1 else "    "
        result.append(f"{i+1:4}{marker}{lines[i]}")
    return '\n'.join(result)

def build_project() -> tuple[bool, str]:
    """Build the Lean project."""
    env = os.environ.copy()
    env["PATH"] = f"{os.environ.get('HOME', '')}/.elan/bin:{env.get('PATH', '')}"
    
    try:
        result = subprocess.run(
            ["lake", "build"],
            cwd=BASE_DIR,
            capture_output=True,
            text=True,
            timeout=300,
            env=env
        )
        return result.returncode == 0, result.stdout + result.stderr
    except Exception as e:
        return False, str(e)

def extract_proof_from_response(response: str) -> str:
    """Extract just the proof code from the response."""
    text = response.strip()
    
    # Remove markdown code blocks
    if "```lean" in text:
        start = text.find("```lean") + 7
        end = text.find("```", start)
        if end > start:
            text = text[start:end].strip()
    elif "```" in text:
        start = text.find("```") + 3
        end = text.find("```", start)
        if end > start:
            text = text[start:end].strip()
    
    # Remove any leading "by" if present (we'll add it ourselves)
    text = text.strip()
    if text.startswith("by\n") or text.startswith("by "):
        text = text[2:].strip()
    
    return text

def replace_sorry_in_file(file_path: str, line_num: int, new_proof: str) -> str:
    """Replace the sorry with the new proof, return the new file content."""
    content = load_file(file_path)
    lines = content.split('\n')
    
    sorry_line = lines[line_num - 1]
    indent = len(sorry_line) - len(sorry_line.lstrip())
    indent_str = ' ' * indent
    
    # Check if sorry is part of a "by sorry" or standalone
    if 'sorry' in sorry_line:
        # Replace just the sorry with the proof
        # If proof is multiline, handle indentation
        proof_lines = new_proof.split('\n')
        if len(proof_lines) == 1:
            new_line = sorry_line.replace('sorry', new_proof.strip())
        else:
            # Multiline proof - replace sorry line with indented proof
            indented_proof = '\n'.join(indent_str + l.strip() for l in proof_lines if l.strip())
            new_line = indented_proof
        
        lines[line_num - 1] = new_line
        return '\n'.join(lines)
    
    return content  # No change if sorry not found

async def prove_single_sorry(client: anthropic.AsyncAnthropic, file_path: str, line_num: int, paper: str) -> bool:
    """Attempt to prove a single sorry."""
    print(f"\n{'='*60}")
    print(f"Working on: {file_path}:{line_num}")
    print(f"{'='*60}")
    
    # Backup the file
    backup_file(file_path)
    
    # Load context
    lean_file = load_file(file_path)
    context = get_surrounding_context(file_path, line_num)
    
    system_prompt = """You are an expert Lean 4 mathematician formalizing the Hodge Conjecture.

Your task: Replace a "sorry" statement with a valid Lean 4 proof.

You have:
1. The COMPLETE mathematical paper with all proofs (LaTeX)
2. The COMPLETE Lean file with all definitions
3. The specific location of the sorry

CRITICAL RULES:
1. Output ONLY the Lean proof code that replaces "sorry"
2. Do NOT include theorem signatures, only the proof body
3. Use tactics available in Lean 4 + Mathlib
4. If you need a helper lemma, use "have" with sorry, then explain
5. Keep proofs simple and direct when possible

COMMON TACTICS:
- simp, simp only [...], simp_all
- rfl, rw [...], exact, apply
- intro, intros, constructor
- cases, induction, match
- use, obtain, have, let
- norm_num, ring, linarith
- sorry (as last resort for sub-goals)

OUTPUT: Just the proof code, starting right after ":= by" """

    user_message = f"""# MATHEMATICAL PAPER (Complete LaTeX source)

{paper[:50000]}  # First 50k chars to stay within limits

# LEAN FILE: {file_path}

{lean_file}

# SORRY LOCATION (line {line_num} marked with >>>)

{context}

# TASK

Replace the "sorry" at line {line_num} with a valid Lean 4 proof.
Study the paper for the mathematical argument, then translate to Lean.

Output ONLY the proof code."""

    for iteration in range(MAX_ITERATIONS):
        print(f"  Iteration {iteration + 1}/{MAX_ITERATIONS}")
        
        try:
            response = await asyncio.wait_for(
                client.messages.create(
                    model=MODEL,
                    max_tokens=4096,
                    system=system_prompt,
                    messages=[{"role": "user", "content": user_message}]
                ),
                timeout=API_TIMEOUT
            )
            
            raw_proof = response.content[0].text.strip()
            proof = extract_proof_from_response(raw_proof)
            
            print(f"  Proposed proof ({len(proof)} chars): {proof[:100]}...")
            
            # Apply the proof
            new_content = replace_sorry_in_file(file_path, line_num, proof)
            save_file(file_path, new_content)
            
            # Build and check
            success, output = build_project()
            
            if success:
                print(f"  ✅ SUCCESS!")
                # Remove backup
                backup_path = os.path.join(BASE_DIR, file_path) + ".backup"
                if os.path.exists(backup_path):
                    os.remove(backup_path)
                return True
            else:
                # Extract errors
                error_lines = [l for l in output.split('\n') if 'error' in l.lower()][:5]
                error_msg = '\n'.join(error_lines) if error_lines else "Build failed"
                print(f"  Build error: {error_msg[:200]}")
                
                # Restore and try again
                restore_file(file_path)
                
                # Update prompt with error feedback
                user_message = f"""Previous attempt failed:
{error_msg}

Please try a different approach. Common issues:
- Wrong lemma names (check Mathlib docs)
- Type mismatches (ℝ vs ℂ)
- Missing imports or instances

Original task: prove sorry at {file_path}:{line_num}
Output ONLY Lean proof code."""

        except asyncio.TimeoutError:
            print(f"  Timeout")
        except Exception as e:
            print(f"  Error: {e}")
            restore_file(file_path)
    
    print(f"  ❌ Failed after {MAX_ITERATIONS} iterations")
    restore_file(file_path)
    return False

async def main():
    print("="*70)
    print("SEQUENTIAL PROVER - Full Context Agents")
    print("="*70)
    
    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        print("ERROR: ANTHROPIC_API_KEY not set")
        sys.exit(1)
    
    client = anthropic.AsyncAnthropic(api_key=api_key)
    
    # Load paper once
    print("Loading mathematical paper...")
    paper = get_full_paper()
    print(f"Paper loaded: {len(paper)} characters")
    
    # Find remaining sorries
    sorries = get_remaining_sorries()
    print(f"\nFound {len(sorries)} remaining sorries:")
    for s in sorries:
        print(f"  - {s['file']}:{s['line']}")
    
    # Process each sorry
    successes = 0
    for i, sorry in enumerate(sorries):
        print(f"\n[{i+1}/{len(sorries)}] Processing {sorry['file']}:{sorry['line']}")
        
        if await prove_single_sorry(client, sorry['file'], sorry['line'], paper):
            successes += 1
            print(f"Progress: {successes}/{i+1} succeeded")
        else:
            print(f"Moving to next sorry...")
    
    print("\n" + "="*70)
    print(f"FINAL: {successes}/{len(sorries)} sorries eliminated")
    print("="*70)

if __name__ == "__main__":
    asyncio.run(main())
