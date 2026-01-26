#!/usr/bin/env python3
"""
Targeted Lean Prover Agent

This agent can ONLY replace 'sorry' with actual proofs.
It cannot modify definitions - it can only fill in proof bodies.

Key difference from native_prover:
- Extracts only the theorem/proof context around the sorry
- Generates only the proof body (what goes after := by or := ...)
- Replaces just the sorry, not the whole file
"""

import os
import sys
import json
import re
import subprocess
import anthropic
from datetime import datetime

HODGE_DIR = "/home/ubuntu/hodge"
MAX_ITERATIONS = 30
MODEL = "claude-sonnet-4-20250514"

# Load the full mathematical paper
PAPER_CONTENT = ""
try:
    with open(f"{HODGE_DIR}/JA_hodge_approach_clean_black_FINAL.tex", "r") as f:
        PAPER_CONTENT = f.read()
except:
    pass

def run_command(cmd, cwd=HODGE_DIR, timeout=300):
    """Run a shell command and return stdout, stderr, exit code."""
    try:
        result = subprocess.run(
            cmd, shell=True, cwd=cwd,
            capture_output=True, text=True, timeout=timeout
        )
        return result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired:
        return "", "Command timed out", 1

def read_file(filepath):
    """Read a file from the hodge directory."""
    full_path = os.path.join(HODGE_DIR, filepath)
    try:
        with open(full_path, 'r') as f:
            return f.read()
    except Exception as e:
        return f"Error reading {filepath}: {e}"

def write_file(filepath, content):
    """Write a file to the hodge directory."""
    full_path = os.path.join(HODGE_DIR, filepath)
    try:
        with open(full_path, 'w') as f:
            f.write(content)
        return True
    except Exception as e:
        print(f"Error writing {filepath}: {e}")
        return False

def build_file(lean_file):
    """Build a specific Lean file and return errors."""
    module = lean_file.replace("/", ".").replace(".lean", "")
    cmd = f"export PATH=$HOME/.elan/bin:$PATH && lake build {module} 2>&1"
    stdout, stderr, code = run_command(cmd)
    return stdout + stderr, code == 0

def extract_context(file_content, line_num, context_lines=50):
    """Extract context around a specific line."""
    lines = file_content.split('\n')
    start = max(0, line_num - context_lines)
    end = min(len(lines), line_num + context_lines)
    
    # Find the theorem/lemma containing this sorry
    theorem_start = line_num
    for i in range(line_num, -1, -1):
        if any(kw in lines[i] for kw in ['theorem ', 'lemma ', 'def ', 'instance ']):
            theorem_start = i
            break
    
    # Include from theorem start
    start = min(start, theorem_start)
    
    # Add line numbers for reference
    numbered_lines = []
    for i in range(start, end):
        prefix = ">>> " if i == line_num - 1 else "    "
        numbered_lines.append(f"{prefix}{i+1:4d}| {lines[i]}")
    
    return '\n'.join(numbered_lines), theorem_start, lines

def replace_sorry_with_proof(file_content, line_num, proof_text):
    """Replace the sorry at line_num with the provided proof."""
    lines = file_content.split('\n')
    target_line = lines[line_num - 1]
    
    # Find indentation
    indent = len(target_line) - len(target_line.lstrip())
    indent_str = target_line[:indent]
    
    # Replace sorry with proof
    if 'sorry' in target_line:
        # Check if it's inline sorry (e.g., ":= sorry" or "sorry")
        if ':= sorry' in target_line:
            # Replace with := followed by proof
            new_line = target_line.replace(':= sorry', ':= ' + proof_text.strip())
            lines[line_num - 1] = new_line
        else:
            # Standalone sorry in a by block - replace with proof lines
            proof_lines = proof_text.strip().split('\n')
            # Keep same indentation
            indented_proof = [indent_str + pl.strip() for pl in proof_lines if pl.strip()]
            lines[line_num - 1] = '\n'.join(indented_proof)
    
    return '\n'.join(lines)

def prove_sorry(task):
    """
    Prove a specific sorry at a given line.
    
    task = {
        "file": "Hodge/Analytic/Currents.lean",
        "line": 666,
        "name": "hausdorffIntegrate_bound",
        "description": "Prove |∫_Z ω| ≤ mass(Z) · comass(ω)",
    }
    """
    client = anthropic.Anthropic()
    
    file_path = task["file"]
    line_num = task["line"]
    theorem_name = task["name"]
    description = task["description"]
    context_info = task.get("context", "")
    
    print(f"\n{'='*60}")
    print(f"PROVING: {theorem_name}")
    print(f"FILE: {file_path}")
    print(f"LINE: {line_num}")
    print(f"DESCRIPTION: {description}")
    print(f"{'='*60}\n")
    
    # Read the file
    original_content = read_file(file_path)
    if "Error reading" in original_content:
        print(f"Failed to read file: {original_content}")
        return False, 0
    
    # Extract context around the sorry
    context, theorem_start, lines = extract_context(original_content, line_num)
    
    # Initial build to see current state
    build_output, _ = build_file(file_path)
    
    # Build system prompt with paper content
    paper_section = PAPER_CONTENT[:50000] if PAPER_CONTENT else "Paper not available"
    context_section = f"## Additional Context\n{context_info}" if context_info else ""
    
    system_prompt = f"""You are an expert Lean 4 prover working on the Hodge Conjecture formalization.

## Your Task
Prove the theorem `{theorem_name}` by replacing the 'sorry' with an actual proof.

## Description
{description}

{context_section}

## The Full Mathematical Paper (LaTeX)
Below is the complete mathematical paper containing all proofs. Use it as reference.

{paper_section}

## CRITICAL RULES
1. You can ONLY output proof tactics/terms to replace the sorry
2. You CANNOT change definitions - only fill in proofs  
3. Use Mathlib lemmas - search the paper for mathematical arguments
4. The paper has the proofs - translate them to Lean

## Output Format
Output ONLY the proof body in a code block:
```proof
<your proof tactics here>
```

The proof body will replace the `sorry` exactly.
"""

    # Initial message
    initial_msg = f"""Here is the context around the sorry (line {line_num} marked with >>>):

```lean
{context}
```

Current build output (may have errors):
```
{build_output[-3000:]}
```

Please provide a proof to replace the sorry at line {line_num}."""

    conversation = [{"role": "user", "content": initial_msg}]
    
    for iteration in range(MAX_ITERATIONS):
        print(f"\n--- Iteration {iteration + 1}/{MAX_ITERATIONS} ---")
        
        try:
            response = client.messages.create(
                model=MODEL,
                max_tokens=8000,
                system=system_prompt,
                messages=conversation
            )
            
            assistant_msg = response.content[0].text
            conversation.append({"role": "assistant", "content": assistant_msg})
            
        except Exception as e:
            print(f"API error: {e}")
            continue
        
        # Extract proof from response
        proof_match = re.search(r'```proof\n(.*?)\n```', assistant_msg, re.DOTALL)
        if not proof_match:
            # Try alternative formats
            proof_match = re.search(r'```lean\n(.*?)\n```', assistant_msg, re.DOTALL)
        if not proof_match:
            proof_match = re.search(r'```\n(.*?)\n```', assistant_msg, re.DOTALL)
        
        if proof_match:
            proof_text = proof_match.group(1).strip()
            print(f"Extracted proof: {proof_text[:100]}...")
            
            # Read current file state
            current_content = read_file(file_path)
            
            # Apply the proof
            new_content = replace_sorry_with_proof(current_content, line_num, proof_text)
            
            # Write the modified file
            write_file(file_path, new_content)
            
            # Build
            print("Building...")
            build_output, success = build_file(file_path)
            
            # Check if this specific sorry is gone
            new_file = read_file(file_path)
            new_lines = new_file.split('\n')
            sorry_still_there = 'sorry' in new_lines[line_num - 1] if line_num <= len(new_lines) else False
            
            if success and not sorry_still_there:
                # Re-read and check the line
                final_content = read_file(file_path)
                if 'sorry' not in final_content.split('\n')[line_num - 1] if line_num <= len(final_content.split('\n')) else True:
                    print(f"\n✅ SUCCESS! {theorem_name} proved!")
                    return True, iteration + 1
            
            # Prepare feedback
            feedback = f"""Build result:
```
{build_output[-2500:]}
```

{"Build succeeded but the sorry is still there. Please provide a complete proof." if success else "Build failed. Please fix your proof."}

The current state of line {line_num}: `{new_lines[line_num-1] if line_num <= len(new_lines) else 'N/A'}`"""

            conversation.append({"role": "user", "content": feedback})
        else:
            print("No proof found in response")
            conversation.append({"role": "user", "content": "I couldn't find a proof in your response. Please provide the proof in a ```proof block."})
        
        # Truncate conversation if too long
        if len(conversation) > 16:
            conversation = conversation[:2] + conversation[-14:]
    
    # Restore original on failure
    print(f"\n❌ FAILED after {MAX_ITERATIONS} iterations. Restoring original file.")
    write_file(file_path, original_content)
    return False, MAX_ITERATIONS

def main():
    if len(sys.argv) < 2:
        print("Usage: python targeted_prover.py <task_json>")
        print("  or: python targeted_prover.py --test")
        sys.exit(1)
    
    if sys.argv[1] == "--test":
        # Test with integrate_linear which should be simpler
        task = {
            "file": "Hodge/Analytic/Currents.lean",
            "line": 828,
            "name": "integrate_linear_rectifiable",
            "description": "Prove linearity of integration: ∫_Z (c·ω₁ + ω₂) = c·∫_Z ω₁ + ∫_Z ω₂",
            "context": """hausdorffIntegrate is defined as:
(∫ x in data.carrier, formVectorPairing ω data.orientation x ∂data.measure).re

Linearity should follow from:
1. MeasureTheory.integral_add - linearity of Bochner integral
2. MeasureTheory.integral_smul - scalar multiplication
3. Complex.re is linear (Complex.re_add, Complex.re_smul)
4. formVectorPairing is linear in the form argument
"""
        }
    else:
        task = json.loads(sys.argv[1])
    
    success, iterations = prove_sorry(task)
    
    result = {
        "task": task,
        "success": success,
        "iterations": iterations,
        "timestamp": datetime.now().isoformat()
    }
    
    print(f"\nResult: {json.dumps(result, indent=2)}")

if __name__ == "__main__":
    main()
