#!/usr/bin/env python3
"""
Robust Prover - Single sorry at a time with proper file handling.

Key improvements:
1. Works on ONE sorry at a time
2. Creates full file backup before any modification  
3. Always restores from backup on failure
4. Only moves to next sorry after confirmed success
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
API_TIMEOUT = 300  # 5 minutes
MAX_ITERATIONS = 15
MODEL = "claude-sonnet-4-20250514"

BASE_DIR = "/home/ubuntu/hodge"
BACKUP_DIR = "/home/ubuntu/hodge_backup"

def run_cmd(cmd, cwd=None, timeout=300):
    """Run a command and return (success, output)."""
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

def find_sorries():
    """Find all remaining sorries."""
    success, output = run_cmd("grep -rn '^\\s*sorry' Hodge/ --include='*.lean'")
    sorries = []
    for line in output.strip().split('\n'):
        if line and ':' in line:
            parts = line.split(':')
            if len(parts) >= 2:
                sorries.append({
                    "file": parts[0],
                    "line": int(parts[1]),
                    "context": ':'.join(parts[2:]) if len(parts) > 2 else ""
                })
    return sorries

def create_full_backup():
    """Create a full backup of Hodge/ directory."""
    if os.path.exists(BACKUP_DIR):
        shutil.rmtree(BACKUP_DIR)
    shutil.copytree(f"{BASE_DIR}/Hodge", BACKUP_DIR)
    print(f"Created full backup at {BACKUP_DIR}")

def restore_from_backup():
    """Restore Hodge/ from backup."""
    if os.path.exists(BACKUP_DIR):
        shutil.rmtree(f"{BASE_DIR}/Hodge")
        shutil.copytree(BACKUP_DIR, f"{BASE_DIR}/Hodge")
        print("Restored from backup")
        return True
    return False

def load_file(path):
    """Load file contents."""
    full_path = f"{BASE_DIR}/{path}" if not path.startswith('/') else path
    with open(full_path, 'r') as f:
        return f.read()

def save_file(path, content):
    """Save content to file."""
    full_path = f"{BASE_DIR}/{path}" if not path.startswith('/') else path
    with open(full_path, 'w') as f:
        f.write(content)

def get_context(file_path, line_num, before=60, after=30):
    """Get context around a line."""
    content = load_file(file_path)
    lines = content.split('\n')
    start = max(0, line_num - before - 1)
    end = min(len(lines), line_num + after)
    
    result = []
    for i in range(start, end):
        marker = ">>> " if i == line_num - 1 else "    "
        result.append(f"{i+1:4}{marker}{lines[i]}")
    return '\n'.join(result)

def replace_sorry(file_path, line_num, new_proof):
    """Replace sorry at line_num with new_proof."""
    content = load_file(file_path)
    lines = content.split('\n')
    
    if line_num - 1 >= len(lines):
        return False
    
    old_line = lines[line_num - 1]
    if 'sorry' not in old_line:
        return False
    
    # Get indentation
    indent = len(old_line) - len(old_line.lstrip())
    indent_str = ' ' * indent
    
    # Handle the replacement
    proof_lines = new_proof.strip().split('\n')
    if len(proof_lines) == 1:
        # Single line proof
        new_line = old_line.replace('sorry', proof_lines[0].strip())
        lines[line_num - 1] = new_line
    else:
        # Multi-line proof - replace the sorry line entirely
        indented_proof = '\n'.join(indent_str + line.strip() for line in proof_lines)
        lines[line_num - 1] = indented_proof
    
    save_file(file_path, '\n'.join(lines))
    return True

def build_project():
    """Build and return (success, errors)."""
    success, output = run_cmd("lake build", timeout=300)
    if success:
        return True, ""
    
    # Extract error lines
    error_lines = [l for l in output.split('\n') if 'error' in l.lower()][:10]
    return False, '\n'.join(error_lines)

def get_paper():
    """Load the mathematical paper."""
    paths = [
        f"{BASE_DIR}/tex/archive/JA_hodge_approach_clean_black_FINAL.tex",
        f"{BASE_DIR}/JA_hodge_approach_clean_black_FINAL.tex"
    ]
    for p in paths:
        if os.path.exists(p):
            with open(p, 'r') as f:
                return f.read()
    return "Paper not found"

async def prove_sorry(client, file_path, line_num, paper):
    """Attempt to prove a single sorry."""
    print(f"\n{'='*60}")
    print(f"TARGET: {file_path}:{line_num}")
    print(f"{'='*60}")
    
    # Load context
    lean_file = load_file(file_path)
    context = get_context(file_path, line_num)
    
    system_prompt = """You are an expert Lean 4 mathematician. Your task is to replace a "sorry" with a valid proof.

RULES:
1. Output ONLY the Lean code that replaces "sorry"
2. Do NOT include theorem signatures
3. Keep proofs simple when possible
4. Use standard Mathlib tactics

TACTICS: simp, rfl, exact, apply, intro, constructor, cases, use, have, let, sorry (if truly stuck)

Output ONLY proof code, no explanations."""

    # Truncate paper to fit in context
    paper_excerpt = paper[:40000] if len(paper) > 40000 else paper
    
    user_msg = f"""LEAN FILE: {file_path}

{lean_file}

SORRY AT LINE {line_num} (marked >>>):
{context}

MATHEMATICAL REFERENCE (excerpt):
{paper_excerpt}

Replace the sorry with valid Lean 4 proof code."""

    for iteration in range(MAX_ITERATIONS):
        print(f"  Attempt {iteration + 1}/{MAX_ITERATIONS}")
        
        try:
            response = await asyncio.wait_for(
                client.messages.create(
                    model=MODEL,
                    max_tokens=2048,
                    system=system_prompt,
                    messages=[{"role": "user", "content": user_msg}]
                ),
                timeout=API_TIMEOUT
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up
            if "```" in proof:
                lines = proof.split('\n')
                clean_lines = []
                in_code = False
                for line in lines:
                    if line.startswith("```"):
                        in_code = not in_code
                    elif in_code:
                        clean_lines.append(line)
                proof = '\n'.join(clean_lines) if clean_lines else proof
            
            print(f"  Proof: {proof[:80]}...")
            
            # Try the proof
            if replace_sorry(file_path, line_num, proof):
                success, errors = build_project()
                
                if success:
                    print(f"  ✅ SUCCESS!")
                    # Update backup with this success
                    create_full_backup()
                    return True
                else:
                    print(f"  Build failed: {errors[:150]}")
                    # Restore and try again
                    restore_from_backup()
                    user_msg = f"""Previous attempt failed:
{errors}

Try a different approach. Original task: prove sorry at {file_path}:{line_num}
Output ONLY Lean proof code."""
            else:
                print(f"  Failed to replace sorry")
                restore_from_backup()
                
        except asyncio.TimeoutError:
            print(f"  Timeout")
            restore_from_backup()
        except Exception as e:
            print(f"  Error: {e}")
            restore_from_backup()
    
    print(f"  ❌ Failed after {MAX_ITERATIONS} attempts")
    restore_from_backup()
    return False

async def main():
    print("="*60)
    print("ROBUST PROVER")
    print("="*60)
    
    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        print("ERROR: ANTHROPIC_API_KEY not set")
        sys.exit(1)
    
    client = anthropic.AsyncAnthropic(api_key=api_key)
    
    # First verify build is clean
    print("Verifying build...")
    success, _ = build_project()
    if not success:
        print("ERROR: Build is not clean! Fix errors first.")
        sys.exit(1)
    print("Build verified clean.")
    
    # Create initial backup
    create_full_backup()
    
    # Load paper
    print("Loading paper...")
    paper = get_paper()
    print(f"Paper: {len(paper)} chars")
    
    # Find sorries
    sorries = find_sorries()
    print(f"\nFound {len(sorries)} sorries:")
    for s in sorries:
        print(f"  {s['file']}:{s['line']}")
    
    # Process one at a time
    successes = 0
    for i, sorry in enumerate(sorries):
        print(f"\n[{i+1}/{len(sorries)}]")
        if await prove_sorry(client, sorry['file'], sorry['line'], paper):
            successes += 1
    
    print(f"\n{'='*60}")
    print(f"FINAL: {successes}/{len(sorries)} eliminated")
    print(f"{'='*60}")
    
    # Show remaining
    remaining = find_sorries()
    if remaining:
        print(f"\nRemaining sorries ({len(remaining)}):")
        for s in remaining:
            print(f"  {s['file']}:{s['line']}")

if __name__ == "__main__":
    asyncio.run(main())
