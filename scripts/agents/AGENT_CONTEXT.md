# CRITICAL AGENT CONTEXT (Updated 2026-01-30)

This repo is a Lean 4 formalization of the Hodge conjecture. The proof track is **green** and the
remaining "deep content" is isolated in the **Deep Track** (`Hodge/Deep/`).

## 0. Build rule (repo-specific)

**Before any `lake build`, run:**

```bash
lake exe cache get
```

## 1. TWO TRACKS: Proof Track vs Deep Track

### Proof Track (COMPLETE — do not touch unless asked)
- **Main theorem**: `hodge_conjecture` in `Hodge/Main.lean`
- **Axioms**: Only `[propext, Classical.choice, Quot.sound]` ✅
- **Status**: Kernel-unconditional (via stub instances)

### Deep Track (YOUR WORK GOES HERE)
- **Build target**: `lake build Hodge.Deep`
- **Files**: `Hodge/Deep/Pillars/*.lean`
- **Goal**: Replace `sorry` with real proofs

## 2. DEEP TRACK PILLARS (Priority Order)

| Pillar | File | Sorries | Description |
|--------|------|---------|-------------|
| **Stokes** | `Hodge/Deep/Pillars/Stokes.lean` | ~7 | Hausdorff measure, submanifold integration |
| **Microstructure** | `Hodge/Deep/Pillars/Microstructure.lean` | ~6 | Cubulation, sheets, gluing, defect→0 |
| **Harvey-Lawson** | `Hodge/Deep/Pillars/HarveyLawson.lean` | ~5 | Calibrated current → analytic variety |
| **GAGA** | `Hodge/Deep/Pillars/GAGA.lean` | ~4 | Strong analytic/algebraic sets, Chow theorem |
| **Federer-Fleming** | `Hodge/Deep/Pillars/FedererFleming.lean` | ~6 | Flat compactness, cycles preserved |
| **Poincaré Duality** | `Hodge/Deep/Pillars/PoincareDuality.lean` | ~5 | Integration current, fundamental class |

## 3. HARD RULES — READ CAREFULLY

### ❌ NEVER DO THESE:
1. **Never use `admit`**
2. **Never trivialize**: No `:= trivial`, `:= True`, `:= ⟨⟩`, `:= by simp`, `:= rfl` for deep theorems
3. **Never weaken statement types** — the goal types are locked
4. **Never add new `.universal` instances** that bypass the work
5. **Never replace `sorry` with `trivial`** — that defeats the purpose

### ✅ ALWAYS DO THESE:
1. **Prove actual mathematical content** — use Mathlib lemmas
2. **Document TeX references** — cite which paper proposition you're proving
3. **Build incrementally** — prove helper lemmas first
4. **Run `lake build Hodge.Deep`** after each change

## 4. How to Work on a Pillar

```bash
# 1. Get Mathlib cache
lake exe cache get

# 2. Build the deep track to see current sorry count
lake build Hodge.Deep 2>&1 | grep -c "declaration uses 'sorry'"

# 3. Pick a pillar file, find a sorry, prove it
# Example: Hodge/Deep/Pillars/Stokes.lean

# 4. Rebuild to verify
lake build Hodge.Deep
```

## 5. What Success Looks Like

- **Before**: `warning: Hodge/Deep/Pillars/Stokes.lean:55:4: declaration uses 'sorry'`
- **After**: No warning for that line

When a pillar has 0 sorries, the `.real` instance can replace the `.universal` stub.

## 6. Mathlib Patterns for Deep Work

### Hausdorff Measure
```lean
import Mathlib.MeasureTheory.Measure.Hausdorff

-- Use MeasureTheory.Measure.hausdorffMeasure
-- Finite on compact sets in finite dimensions
```

### Submanifold Integration
```lean
-- Build using MeasureTheory.Integral.Lebesgue
-- Key: mass-comass duality |∫_Z ω| ≤ mass(Z) · ‖ω‖
```

### Compactness Arguments
```lean
-- Use IsCompact.exists_finite_cover for cubulation
-- Use Filter.Tendsto for convergence
```

## 7. Verification Commands

```bash
# Check deep track sorry count
lake build Hodge.Deep 2>&1 | grep "sorry" | wc -l

# Check proof track is still clean
lake env lean Hodge/Utils/DependencyCheck.lean

# Full build
lake build
```

## 8. TeX References

Each deep theorem corresponds to a paper result:
- Stokes: Federer GMT §4.1.7
- Harvey-Lawson: "Calibrated Geometries" (1982)
- GAGA: Serre (1956), Chow (1949)
- Federer-Fleming: "Normal and integral currents" (1960)

Cite the specific proposition in your proof comments.
