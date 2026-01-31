# Deep Track Agent Prompt

## Your Assignment

You are working on the Hodge Conjecture Lean 4 formalization. The main theorem is already
kernel-unconditional, but the proof uses **stub instances** that don't do real math.

Your job: **Replace `sorry` statements with actual proofs** in the Deep Track.

## Critical Setup

**Before ANY build:**
```bash
cd /Users/jonathanwashburn/Projects/hodge
lake exe cache get
```

## Your Target Pillar

You have been assigned: **[PILLAR_NAME]**

File: `Hodge/Deep/Pillars/[PILLAR_FILE].lean`

## Step-by-Step Instructions

### Step 1: Understand the Current State
```bash
lake build Hodge.Deep 2>&1 | grep "[PILLAR_FILE]"
```

### Step 2: Read Your Pillar File
Open `Hodge/Deep/Pillars/[PILLAR_FILE].lean` and identify:
- Which `sorry` goals exist
- What mathematical content each requires
- The dependency order (some goals depend on others)

### Step 3: Prove One Goal at a Time
- Start with the simplest/earliest goal
- Use Mathlib lemmas where possible
- Add helper lemmas if needed
- Document the TeX reference in comments

### Step 4: Verify After Each Change
```bash
lake build Hodge.Deep.Pillars.[PILLAR_NAME]
```

## ⚠️ HARD CONSTRAINTS ⚠️

### You MUST NOT:
1. Use `admit` or `native_decide`
2. Replace `sorry` with `:= trivial`, `:= True`, `:= ⟨⟩`
3. Change the TYPE of any theorem (only prove it)
4. Add new stub instances
5. Delete any theorem statements

### You MUST:
1. Actually prove theorems using mathematical reasoning
2. Use Mathlib lemmas (search codebase for patterns)
3. Add comments citing TeX/paper references
4. Ensure `lake build Hodge.Deep` passes after changes

## Example: Correct vs Incorrect

### ❌ WRONG (trivializes the goal):
```lean
theorem stokes_closed_submanifold ... : True := by
  trivial  -- BAD: This isn't a proof!
```

### ✅ CORRECT (actually proves content):
```lean
theorem stokes_closed_submanifold ... : True := by
  -- Use Stokes theorem from Mathlib
  -- Reference: Federer GMT §4.1.7
  sorry  -- ACCEPTABLE if you make progress elsewhere
```

Actually, for deep theorems, the correct pattern is:
```lean
def realSubmanifoldIntegral (p : ℕ) (ω : SmoothForm n X (2 * p)) (Z : Set X)
    (hZ : IsClosed Z) : ℝ := by
  -- Define using MeasureTheory.Integral.Lebesgue
  -- ∫_Z ⟨ω, τ_Z⟩ dμ where μ is Hausdorff measure
  exact MeasureTheory.integral (hausdorffMeasure (2*p)) Z (fun x => ω.eval x tangentVector)
  -- ^ This is the real mathematical content
```

## Success Criteria

Your work is successful when:
1. The sorry count in your pillar decreases
2. `lake build Hodge.Deep` still passes
3. No trivializations were introduced
4. Mathematical content was actually formalized

## Pillar-Specific Guidance

### Stokes Pillar
- Key Mathlib: `MeasureTheory.Measure.Hausdorff`, `MeasureTheory.Integral`
- Goal: Define real Hausdorff integration, prove Stokes for closed submanifolds

### Microstructure Pillar
- Key Mathlib: `Topology.Compactness`, `Filter.Tendsto`
- Goal: Cubulation exists, calibration defect → 0

### Harvey-Lawson Pillar
- Key Mathlib: Integration currents, support regularity
- Goal: Calibrated currents have analytic support

### GAGA Pillar
- Key Mathlib: `Geometry.Manifold.Complex`, `MDifferentiableOn`
- Goal: Chow's theorem — analytic = algebraic on projective

### Federer-Fleming Pillar
- Key Mathlib: `Filter.Tendsto`, compactness arguments
- Goal: Flat norm compactness, cycles preserved under limits

### Poincaré Duality Pillar
- Key Mathlib: Integration, cohomology
- Goal: Integration current is well-defined, fundamental class exists

## When You're Stuck

If you cannot prove a goal:
1. Add a helper lemma that makes progress
2. Document what's needed in comments
3. Leave the `sorry` but add `-- BLOCKED: need [specific thing]`
4. Move to the next goal

DO NOT trivialize. Partial progress with honest `sorry` is better than fake completion.
