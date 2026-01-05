# Hodge Conjecture Lean Proof - Session Prompt

## Instructions for AI Assistant

You are helping to complete a Lean 4 formalization of the Hodge Conjecture proof. 

### Before Making Any Changes

1. **Read the full proof bundle**: `@LEAN_PROOF_BUNDLE.txt`
2. **Create the session snapshot** (automatic): run `./scripts/generate_lean_source.sh`
   - This regenerates `LEAN_PROOF_BUNDLE.txt` and creates `SESSION_YYYYMMDD_HHMMSS_LEAN_PROOF.txt`
2. **Check current status**: Note the sorry count and axiom count at the top
3. **Understand the goal**: The proof is STRUCTURALLY COMPLETE - focus on cleanup
4. **Reference the TeX proof**: `@Hodge-v6-w-Jon-Update-MERGED.tex` for mathematical guidance

### Ground Rules

1. **DO NOT go backwards**: 
   - Current baseline: **0 sorries, 9 axioms** (all 9 used by `hodge_conjecture'`)
   - Keep it that way: don’t reintroduce sorries; don’t add axioms unless replacing more severe stubs
   
2. **Build only files you edit**: 
   ```bash
   lake build Hodge.Path.To.File
   ```
   Do NOT run full `lake build`

3. **Priority order for improvements**:
   - **Staged Mathlib migration**: replace semantic stubs (d/∧/cohomology) with Mathlib-backed definitions
   - Convert classical axioms to theorems only when upstream support exists
   - Keep the main proof compiling at all times (no regressions)

4. **After each change**:
   - Build the specific file
   - Verify: `lake build Hodge.Utils.AuditAxioms` to see used axioms

### Current Proof Status

**STRUCTURALLY COMPLETE** - The main theorem `hodge_conjecture'` compiles successfully.

```
Axioms in codebase: 9
Axioms USED by hodge_conjecture': 9 (verified via #print axioms)
Sorries: 0
```

### Current “Close the Proof” Strategy (staged)

The Lean proof is closed (0 sorries) but the **foundation layer is still semantically stubbed**.
We close this by a staged migration:

- **Stage 1 (now)**: Replace the placeholder wedge `SmoothForm ⋏` with a Mathlib-backed wedge.
  - Work bottom-up: wedge on fiber alternating maps → wedge on `SmoothForm` → update `kahlerPow`
  - Keep `d` temporarily as-is (still 0) so closedness obligations remain trivial while wedge is migrated.

- **Stage 2**: Replace the placeholder exterior derivative `extDerivLinearMap := 0` with a Mathlib-backed `d`.

- **Stage 3**: Replace the current de Rham quotient/multiplication lemmas with a semantically correct de Rham complex/cohomology backend (local or Mathlib, depending on availability).

### The 9 Classical Pillars (USED AXIOMS)

These are the axioms that `hodge_conjecture'` actually depends on:

| # | Axiom | Location | Mathematical Content |
|---|-------|----------|---------------------|
| 1 | `existence_of_representative_form` | Lefschetz.lean:68 | Hodge Decomposition |
| 2 | `exists_uniform_interior_radius` | Cone.lean:104 | Kähler cone interior |
| 3 | `hard_lefschetz_bijective` | Lefschetz.lean:45 | Hard Lefschetz Theorem |
| 4 | `hard_lefschetz_pp_bijective` | Lefschetz.lean:60 | HL preserves (p,p) type |
| 5 | `hard_lefschetz_rational_bijective` | Lefschetz.lean:52 | HL preserves rationality |
| 6 | `harvey_lawson_fundamental_class` | Main.lean:144 | GMT structure theorem |
| 7 | `mass_lsc` | Calibration.lean:129 | Mass semicontinuity |
| 8 | `omega_pow_algebraic` | Main.lean:219 | ω^p is algebraic |
| 9 | `serre_gaga` | GAGA.lean:160 | GAGA principle |

### Current Sorries

None (sorry count is 0).

### Proof Dependency Tree

```
hodge_conjecture'
├── Case p ≤ n/2:
│   ├── signed_decomposition
│   │   └── exists_uniform_interior_radius [AXIOM]
│   ├── cone_positive_represents
│   │   ├── limit_is_calibrated
│   │   │   └── mass_lsc [AXIOM]
│   │   ├── harvey_lawson_union_is_algebraic
│   │   │   └── serre_gaga [AXIOM]
│   │   └── harvey_lawson_fundamental_class [AXIOM]
│   └── omega_pow_algebraic [AXIOM]
│
└── Case p > n/2:
    └── hard_lefschetz_inverse_form
        ├── hard_lefschetz_bijective [AXIOM]
        ├── hard_lefschetz_pp_bijective [AXIOM]
        ├── hard_lefschetz_rational_bijective [AXIOM]
        └── existence_of_representative_form [AXIOM]
```

### Regenerating the Proof Bundle

After making changes, regenerate:
```bash
./scripts/generate_lean_source.sh
```

### Verifying Axiom Usage

To see exactly which axioms the main theorem uses:
```bash
lake build Hodge.Utils.AuditAxioms 2>&1 | grep "depends on axioms"
```

### Success Criteria

- **Current state**: **0 sorries, 9 axioms** ✓
- **Next**: only reduce axioms by replacing pillars with theorems (or strengthening existing stubs)
- **Documentation**: ensure all 9 classical pillars are well-documented

---

## Quick Reference Commands

```bash
# Regenerate proof bundle
./scripts/generate_lean_source.sh

# Check sorry count
grep -rn "sorry" Hodge/ --include="*.lean" | grep -v "This sorry" | wc -l

# Check axiom count  
grep -rn "^axiom " Hodge/ --include="*.lean" | wc -l

# See used axioms
lake build Hodge.Utils.AuditAxioms

# Build specific file
lake build Hodge.Kahler.Main

# List all axioms with context
grep -rn "^axiom " Hodge/ --include="*.lean" -A2
```

---

## Session History

| Date | Sorries | Axioms | Notes |
|------|---------|--------|-------|
| Jan 5, 2026 | 0 | 9 (9 used) | All sorries removed; unused axioms removed |
| Earlier | 6 | 14 | Transport axioms converted to theorems |
