#!/usr/bin/env python3
"""
Native Lean Prover Agent

This agent works directly on the server where Lean is installed.
It focuses on proving ONE specific theorem with a tight compile-test-fix loop.

Key features:
1. Works natively - no syncing, no delays
2. Tight loop - compile after every change
3. Error-driven - reads exact Lean errors and fixes them
4. Single focus - one theorem at a time
"""

import os
import sys
import json
import subprocess
import anthropic
from datetime import datetime

# Configuration
HODGE_DIR = "/home/ubuntu/hodge"
MAX_ITERATIONS = 50
MODEL = "claude-opus-4-5-20251101"

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
    # Convert filepath to module name
    module = lean_file.replace("/", ".").replace(".lean", "")
    cmd = f"export PATH=$HOME/.elan/bin:$PATH && lake build {module} 2>&1"
    stdout, stderr, code = run_command(cmd)
    return stdout + stderr, code == 0

def get_lean_errors(build_output, target_file):
    """Extract errors from build output for a specific file."""
    errors = []
    for line in build_output.split("\n"):
        if target_file in line and ("error:" in line or "Error:" in line):
            errors.append(line)
    return errors

def prove_theorem(task):
    """
    Main proving loop for a single theorem.
    
    task = {
        "file": "Hodge/Analytic/Currents.lean",
        "line": 666,
        "name": "hausdorffIntegrate_bound",
        "description": "Prove |∫_Z ω| ≤ mass(Z) · comass(ω)",
        "context": "This is the mass-comass duality inequality from GMT..."
    }
    """
    client = anthropic.Anthropic()
    
    file_path = task["file"]
    theorem_name = task["name"]
    description = task["description"]
    context = task.get("context", "")
    
    print(f"\n{'='*60}")
    print(f"PROVING: {theorem_name}")
    print(f"FILE: {file_path}")
    print(f"DESCRIPTION: {description}")
    print(f"{'='*60}\n")
    
    # Read initial file
    file_content = read_file(file_path)
    
    # Initial build to see current state
    build_output, success = build_file(file_path)
    
    conversation = []
    
    system_prompt = f"""You are an expert Lean 4 prover working on the Hodge Conjecture formalization.

Your task is to prove the theorem `{theorem_name}` in `{file_path}`.

DESCRIPTION: {description}

CONTEXT: {context}

CRITICAL RULES:
1. You MUST output complete, compilable Lean code
2. After each attempt, I will compile it and show you the exact errors
3. Read the errors carefully and fix them precisely
4. Do NOT use sorry - that's what we're trying to eliminate
5. Use Mathlib lemmas when available
6. If stuck, try a different proof strategy

When you want to modify the file, output EXACTLY:
```lean:FILEPATH
COMPLETE FILE CONTENT
```

The file content must be the ENTIRE file, not just the changed part."""

    # Initial message with file content and build status
    initial_msg = f"""Current file content:

```lean
{file_content}
```

Current build output:
```
{build_output[:5000]}
```

Please prove `{theorem_name}`. Output the complete modified file."""

    conversation.append({"role": "user", "content": initial_msg})
    
    for iteration in range(MAX_ITERATIONS):
        print(f"\n--- Iteration {iteration + 1}/{MAX_ITERATIONS} ---")
        
        # Call Claude
        try:
            response = client.messages.create(
                model=MODEL,
                max_tokens=16000,
                system=system_prompt,
                messages=conversation
            )
            
            assistant_msg = response.content[0].text
            conversation.append({"role": "assistant", "content": assistant_msg})
            
        except Exception as e:
            print(f"API error: {e}")
            continue
        
        # Extract code from response
        if "```lean:" in assistant_msg:
            # Parse the file modification
            parts = assistant_msg.split("```lean:")
            for part in parts[1:]:
                if "```" in part:
                    header_and_code = part.split("\n", 1)
                    if len(header_and_code) == 2:
                        filepath = header_and_code[0].strip()
                        code = header_and_code[1].split("```")[0]
                        
                        print(f"Writing to {filepath}...")
                        write_file(filepath, code)
        
        elif "```lean" in assistant_msg:
            # Simple code block - assume it's the target file
            code_match = assistant_msg.split("```lean")[1].split("```")[0]
            if code_match.strip():
                print(f"Writing to {file_path}...")
                write_file(file_path, code_match.strip())
        
        # Build and check
        print("Building...")
        build_output, success = build_file(file_path)
        
        errors = get_lean_errors(build_output, file_path)
        
        if success and "sorry" not in read_file(file_path).lower():
            print(f"\n✅ SUCCESS! {theorem_name} proved!")
            return True, iteration + 1
        
        if success:
            print(f"Build succeeded but sorry still present")
        else:
            print(f"Build failed: {len(errors)} errors")
            for e in errors[:5]:
                print(f"  {e}")
        
        # Prepare next iteration message
        next_msg = f"""Build result:
```
{build_output[-3000:]}
```

{"Build succeeded but sorry is still present. Please complete the proof." if success else "Build failed. Please fix the errors and try again."}"""

        conversation.append({"role": "user", "content": next_msg})
        
        # Keep conversation manageable
        if len(conversation) > 20:
            conversation = conversation[:2] + conversation[-18:]
    
    print(f"\n❌ FAILED after {MAX_ITERATIONS} iterations")
    return False, MAX_ITERATIONS

def main():
    if len(sys.argv) < 2:
        print("Usage: python native_prover.py <task_json>")
        print("  or: python native_prover.py --test")
        sys.exit(1)
    
    if sys.argv[1] == "--test":
        # Test with a simple task
        task = {
            "file": "Hodge/Analytic/Currents.lean",
            "line": 666,
            "name": "hausdorffIntegrate_bound",
            "description": "Prove the mass-comass inequality: |∫_Z ω| ≤ mass(Z) · comass(ω)",
            "context": """This is a fundamental GMT inequality.

The definition is:
hausdorffIntegrate data ω = (∫ x in data.carrier, formVectorPairing ω data.orientation x ∂data.measure).re

We need to show |hausdorffIntegrate data ω| ≤ data.mass * comass ω

where data.mass = (data.measure data.carrier).toReal

This follows from:
1. |∫ f dμ| ≤ ∫ |f| dμ (triangle inequality for integrals)
2. |formVectorPairing ω τ| ≤ comass(ω) when τ is unit (definition of comass)
3. data.mass = μ(Z)
"""
        }
    else:
        task = json.loads(sys.argv[1])
    
    success, iterations = prove_theorem(task)
    
    result = {
        "task": task,
        "success": success,
        "iterations": iterations,
        "timestamp": datetime.now().isoformat()
    }
    
    print(f"\nResult: {json.dumps(result, indent=2)}")
    
    # Save result
    result_file = f"proof_results/{task['name']}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    os.makedirs("proof_results", exist_ok=True)
    with open(os.path.join(HODGE_DIR, result_file), 'w') as f:
        json.dump(result, f, indent=2)

if __name__ == "__main__":
    main()
