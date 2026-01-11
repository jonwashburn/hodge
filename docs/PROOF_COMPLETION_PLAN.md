# Hodge Conjecture Formalization: COMPLETE PROOF PLAN

**Document Version**: 2.0  
**Date**: January 11, 2026  
**Goal**: Complete proof with **ZERO custom axioms** and **ZERO sorry statements**

---

## ⚠️ CRITICAL REQUIREMENTS ⚠️

### What We Are Building
A **complete, verified proof** of the Hodge Conjecture that:
- ✅ Compiles with `lake build`
- ✅ Has **NO custom axioms** (only Lean's 3 standard axioms: `propext`, `Classical.choice`, `Quot.sound`)
- ✅ Has **NO sorry statements** anywhere on the proof track
- ✅ Every theorem is **actually proved**, not assumed

### What Is NOT Acceptable
- ❌ **Hole‑shuffling**: replacing an unproved dependency with a different unproved dependency (e.g. `sorry → axiom`, `axiom → sorry`, or swapping one axiom for another) and calling that “progress”
- ❌ Completing a task “locally” while the **global proof track** (dependencies of `hodge_conjecture'`) is not strictly closer to axiom/sorry‑free
- ❌ “Classical Pillar” axioms (or “well‑documented” axioms) on the proof track — documentation is not a proof
- ❌ Merging any PR that **adds** new `axiom`/`sorry` on the proof track, even temporarily

### Success Criterion
```bash
echo 'import Hodge.Kahler.Main
#print axioms hodge_conjecture'\'' | lake env lean --stdin

# REQUIRED OUTPUT:
# 'hodge_conjecture'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

If ANY other axiom appears, the proof is **incomplete**.

---

## How We Avoid “Brick‑Laying”: Castle‑Building Workflow

The objective is **the completed proof**, not “finishing a task ticket”. That means our workflow must enforce that the *global* proof is getting closer to completion.

### 0) Definitions
- **Proof track**: the transitive dependency cone of `hodge_conjecture'` (as reported by `#print axioms hodge_conjecture'`).
- **Hole**: any `sorry` or any non-standard `axiom` that appears in `#print axioms hodge_conjecture'`.
- **Progress**: a merge that **reduces** the set of holes on the proof track, or proves infrastructure without increasing that set.

### 1) Allowed Development Technique: Temporary Sorries (YES, but quarantined)
Yes, it can be practical to introduce temporary `sorry` **while exploring** a proof. The key is: **temporary means it does not land on the proof track in main**.

Policy:
- Temporary `sorry`s are allowed **only** in:
  - a feature branch that is not merged until they are gone, or
  - modules that are not imported by `Hodge.Kahler.Main` (not on the proof track).
- Temporary `sorry`s are **never “resolved” by converting them to axioms**.
- If a proof cannot be completed, the output is a **blocker report** (what lemma/API is missing), not a new axiom.

### 2) Merge Gate: Monotone Proof-Track Progress (No Hole‑Shuffling)
Every merge must satisfy:
- **No new proof-track holes** are introduced.
- For “axiom elimination” work: the *named* axiom must disappear from:
  - `#print axioms hodge_conjecture'`, and
  - `grep -rn '^axiom <Name>'` in the relevant file(s),
  and nothing equivalent reappears as a new axiom/sorry.

### 3) Required Checks (run before merging any PR)

```bash
cd /Users/jonathanwashburn/Projects/hodge

# 1) Main build
lake build Hodge.Kahler.Main

# 2) Proof-track hole check (this is the ground truth)
cat > /tmp/axioms.lean << 'EOF'
import Hodge.Kahler.Main
#print axioms hodge_conjecture'
EOF
lake env lean /tmp/axioms.lean

# 3) Proof-track “no sorry” check (coarse, but useful)
grep -rn "sorry" Hodge/Kahler/Main.lean Hodge/Analytic/Forms.lean Hodge/Cohomology/Basic.lean \
  Hodge/Classical/CycleClass.lean Hodge/Classical/GAGA.lean
```

### 4) What an Agent Deliverable Looks Like (high-signal)
An agent’s work is “done” if and only if it results in one of:
- **(Preferred)** A PR that removes a specific proof-track hole with a real proof, and passes the merge gate above.
- **(Acceptable)** A blocker report that states:
  - the exact Lean goal/lemma that is missing,
  - the minimal Mathlib API gap,
  - a proposed local development plan (new lemmas/modules) to fill it,
  - and why this is needed for the global proof.

---

## Current Status

### Proof Track Axioms That Must Be PROVED (11 total)

| # | Axiom | File:Line | Must Be Proved From |
|---|-------|-----------|---------------------|
| 1 | `extDerivLinearMap` | Forms.lean:183 | `mfderiv` + alternatization |
| 2 | `isFormClosed_unitForm` | Forms.lean:364 | `mfderiv_const` = 0 |
| 3 | `isSmoothAlternating_wedge` | Forms.lean:276 | Bilinear map composition |
| 4 | `smoothExtDeriv_extDeriv` | Forms.lean:315 | Symmetry of mixed partials |
| 5 | `smoothExtDeriv_wedge` | Forms.lean:324 | Leibniz rule for derivatives |
| 6 | `poincareDualFormExists` | CycleClass.lean:118 | Integration theory + regularization |
| 7 | `FundamentalClassSet_represents_class` | GAGA.lean:364 | Poincaré duality |
| 8 | `SignedAlgebraicCycle.lefschetz_lift` | GAGA.lean:499 | Hard Lefschetz + algebraicity |
| 9 | `omega_pow_algebraic` | Main.lean:223 | Line bundle theory |
| 10 | `Current.boundary_bound` | Currents.lean | GMT/current theory |
| 11 | `cohomologous_wedge` | Basic.lean:228 | Leibniz rule |

---

## Part 1: Differential Forms Infrastructure

### Task 1.1: Prove `extDerivLinearMap`
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 8-16 hours  
**File**: `Hodge/Analytic/Forms.lean`

**Current (WRONG)**:
```lean
axiom extDerivLinearMap (n : ℕ) (X : Type u) ... : SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1)
```

**Target (CORRECT)**:
```lean
/-- The exterior derivative as a ℂ-linear map, constructed from mfderiv. -/
noncomputable def extDerivLinearMap (n : ℕ) (X : Type u) 
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] 
    [IsManifold (𝓒_complex n) ⊤ X] (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1) where
  toFun ω := ⟨smoothExtDerivAt ω, smoothExtDerivAt_smooth ω⟩
  map_add' ω η := by
    apply SmoothForm.ext
    funext x
    simp only [SmoothForm.add_apply]
    exact smoothExtDerivAt_add ω η x
  map_smul' c ω := by
    apply SmoothForm.ext
    funext x
    simp only [RingHom.id_apply, SmoothForm.smul_apply]
    exact smoothExtDerivAt_smul c ω x
```

**Required Lemmas to Prove**:
1. `smoothExtDerivAt_smooth` - Prove using `ContMDiff` composition
2. `smoothExtDerivAt_add` - Prove using `mfderiv_add`
3. `smoothExtDerivAt_smul` - Prove using `mfderiv_const_smul`

**Mathlib APIs**:
- `Geometry.Manifold.MFDeriv.Basic` - `mfderiv`, `mfderiv_add`, `mfderiv_const_smul`
- `Analysis.NormedSpace.Alternating.Uncurry.Fin` - `alternatizeUncurryFin`

**Agent Instructions**:
```
TASK: PROVE extDerivLinearMap (not axiomatize!)

FILE: Hodge/Analytic/Forms.lean

STRICT REQUIREMENT: The word "axiom" must NOT appear for this definition.
You must construct it as a `def` or `noncomputable def` with complete proofs.

STEPS:
1. Define smoothExtDerivAt using mfderiv + alternatizeUncurryFin
2. PROVE smoothExtDerivAt_smooth (use ContMDiff.comp with smooth functions)
3. PROVE smoothExtDerivAt_add (use mfderiv_add for smooth functions)
4. PROVE smoothExtDerivAt_smul (use mfderiv_const_smul)
5. Construct extDerivLinearMap as LinearMap with proved map_add' and map_smul'

VERIFICATION:
lake build Hodge.Analytic.Forms
grep "^axiom extDerivLinearMap" Hodge/Analytic/Forms.lean  # Must return NOTHING

ACCEPTANCE: 
- File compiles
- NO axiom keyword for extDerivLinearMap
- All proofs complete (no sorry)
```

---

### Task 1.2: Prove `isFormClosed_unitForm`
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 2-4 hours  
**File**: `Hodge/Analytic/Forms.lean`

**Current (WRONG)**:
```lean
axiom isFormClosed_unitForm : IsFormClosed (unitForm (n := n) (X := X))
```

**Target (CORRECT)**:
```lean
theorem isFormClosed_unitForm : IsFormClosed (unitForm (n := n) (X := X)) := by
  unfold IsFormClosed smoothExtDeriv smoothExtDerivAt unitForm
  apply SmoothForm.ext
  funext x
  -- The unit form is constant, so mfderiv = 0
  simp only [mfderiv_const, ContinuousLinearMap.zero_apply]
  exact ContinuousAlternatingMap.alternatizeUncurryFin_zero
```

**Key Insight**: `unitForm` is the constant 1-form, so its derivative is zero.

**Agent Instructions**:
```
TASK: PROVE isFormClosed_unitForm (not axiomatize!)

FILE: Hodge/Analytic/Forms.lean

STRICT REQUIREMENT: Replace "axiom" with "theorem" and provide complete proof.

KEY INSIGHT: unitForm is constant, so mfderiv unitForm = 0 everywhere.
Use mfderiv_const to show the derivative is zero.

VERIFICATION:
grep "^axiom isFormClosed_unitForm" Hodge/Analytic/Forms.lean  # Must return NOTHING
```

---

### Task 1.3: Prove `isSmoothAlternating_wedge`
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 4-8 hours  
**File**: `Hodge/Analytic/Forms.lean`

**Current (WRONG)**:
```lean
axiom isSmoothAlternating_wedge (k l : ℕ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsSmoothAlternating n X (k + l) (fun x => ω.as_alternating x ∧ η.as_alternating x)
```

**Target (CORRECT)**:
```lean
theorem isSmoothAlternating_wedge (k l : ℕ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsSmoothAlternating n X (k + l)
      (fun x => ContinuousAlternatingMap.wedge (ω.as_alternating x) (η.as_alternating x)) := by
  -- wedgeCLM_alt is a continuous bilinear map
  let f := ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l
  -- Composition of smooth with continuous bilinear is smooth
  exact f.contMDiff.comp ω.is_smooth |>.clm_apply η.is_smooth
```

**Key Insight**: `wedgeCLM_alt` is continuous bilinear, composition with smooth is smooth.

---

### Task 1.4: Prove `smoothExtDeriv_extDeriv` (d² = 0)
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 16-32 hours  
**File**: `Hodge/Analytic/Forms.lean`

**Current (WRONG)**:
```lean
axiom smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (smoothExtDeriv ω) = 0
```

**Mathematical Content**:
d²ω = 0 follows from the symmetry of second derivatives:
- ∂²f/∂xᵢ∂xⱼ = ∂²f/∂xⱼ∂xᵢ (Schwarz's theorem)
- When alternatized, symmetric tensors become zero

**Target (CORRECT)**:
```lean
theorem smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (smoothExtDeriv ω) = 0 := by
  apply SmoothForm.ext
  funext x
  simp only [smoothExtDeriv_as_alternating, SmoothForm.zero_apply]
  -- Key: second mfderiv is symmetric, alternatization kills it
  -- Use iteratedFDeriv symmetry + alternatize_symmetric_eq_zero
  sorry -- THIS IS THE HARD PART - needs Schwarz theorem on manifolds
```

**Required Infrastructure**:
1. Symmetry of `iteratedMFDeriv` (may need to build)
2. `alternatize_symmetric_eq_zero` - alternatization of symmetric tensor is 0

**This is one of the hardest proofs. May require building manifold Schwarz theorem.**

---

### Task 1.5: Prove `smoothExtDeriv_wedge` (Leibniz Rule)
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 16-32 hours  
**File**: `Hodge/Analytic/Forms.lean`

**Current (WRONG)**:
```lean
axiom smoothExtDeriv_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    smoothExtDeriv (ω ⋏ η) = (smoothExtDeriv ω) ⋏ η + (-1 : ℂ)^k • (ω ⋏ smoothExtDeriv η)
```

**Mathematical Content**:
d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη

This follows from the product rule for derivatives applied to the wedge.

**Required Infrastructure**:
1. Product rule for `mfderiv` of bilinear maps
2. `alternatizeUncurryFin_wedge_left` and `_right` lemmas
3. Sign conventions for graded algebra

---

### Task 1.6: Prove `cohomologous_wedge`
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 8-16 hours  
**File**: `Hodge/Cohomology/Basic.lean`

**Current (WRONG)**:
```lean
axiom cohomologous_wedge ... : (ω₁ ∧ ω₂) ≈ (ω₁' ∧ ω₂')
```

**Target**: Prove using Leibniz rule (Task 1.5).

If ω₁ - ω₁' = dη₁ and ω₂ - ω₂' = dη₂, then:
ω₁ ∧ ω₂ - ω₁' ∧ ω₂' = d(η₁ ∧ ω₂' + (-1)^k ω₁ ∧ η₂)

**Depends on**: Task 1.5 (Leibniz rule)

---

## Part 2: Geometric Measure Theory

### Task 2.1: Prove `poincareDualFormExists`
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 40-80 hours  
**File**: `Hodge/Classical/CycleClass.lean`

**Current (WRONG)**:
```lean
axiom poincareDualFormExists (n : ℕ) (X : Type u) (p : ℕ) ... (Z : Set X) : PoincareDualFormData n X p Z
```

**Mathematical Content**:
For an algebraic subvariety Z ⊂ X of codimension p, construct the Poincaré dual form η_Z.

**Required Infrastructure** (mostly missing from Mathlib):
1. Integration of differential forms on submanifolds
2. Current theory (distributions on forms)
3. Regularization of currents to smooth forms
4. de Rham theorem connecting integration to cohomology

**This is the HARDEST task. Options**:
- Build GMT from scratch (80+ hours)
- Propose a Mathlib contribution for integration theory
- Find alternative proof route that avoids direct GMT

---

### Task 2.2: Prove `FundamentalClassSet_represents_class`
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 16-32 hours  
**File**: `Hodge/Classical/GAGA.lean`
**Depends on**: Task 2.1

---

### Task 2.3: Prove `Current.boundary_bound`
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 8-16 hours  
**File**: `Hodge/Analytic/Currents.lean`

---

## Part 3: Lefschetz Theory

### Task 3.1: Prove `SignedAlgebraicCycle.lefschetz_lift`
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 24-48 hours  
**File**: `Hodge/Classical/GAGA.lean`

**Mathematical Content**:
The Hard Lefschetz isomorphism preserves algebraicity.
If η is algebraic, then L^k(η) is algebraic.

---

### Task 3.2: Prove `omega_pow_algebraic`
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 16-32 hours  
**File**: `Hodge/Kahler/Main.lean`

**Current (WRONG)**:
```lean
axiom omega_pow_algebraic {p : ℕ} (c : ℚ) (hc : c > 0) : ∃ (Z : Set X), ...
```

**Mathematical Content**:
- ω = c₁(L) for ample line bundle L on projective X
- ω^p represents complete intersection of p hyperplane sections
- These are algebraic subvarieties

---

## Part 4: Parallel Execution Plan

### Phase 1: Foundation (Weeks 1-2)
**5 agents in parallel**

| Agent | Task | Hours | Deliverable |
|-------|------|-------|-------------|
| 1A | Task 1.1: extDerivLinearMap | 8-16 | PROVED def |
| 1B | Task 1.2: isFormClosed_unitForm | 2-4 | PROVED theorem |
| 1C | Task 1.3: isSmoothAlternating_wedge | 4-8 | PROVED theorem |
| 1D | Task 1.4: d² = 0 | 16-32 | PROVED theorem |
| 1E | Task 1.5: Leibniz | 16-32 | PROVED theorem |

### Phase 2: Cohomology (Week 2)
**Depends on Phase 1**

| Agent | Task | Hours | Deliverable |
|-------|------|-------|-------------|
| 2A | Task 1.6: cohomologous_wedge | 8-16 | PROVED theorem |

### Phase 3: GMT (Weeks 2-4)
**Hardest phase**

| Agent | Task | Hours | Deliverable |
|-------|------|-------|-------------|
| 3A | Task 2.1: Poincaré duality | 40-80 | PROVED theorem |
| 3B | Task 2.2: Fundamental class | 16-32 | PROVED theorem |
| 3C | Task 2.3: Boundary bound | 8-16 | PROVED theorem |

### Phase 4: Lefschetz (Weeks 3-4)
**Parallel with Phase 3**

| Agent | Task | Hours | Deliverable |
|-------|------|-------|-------------|
| 4A | Task 3.1: Lefschetz lift | 24-48 | PROVED theorem |
| 4B | Task 3.2: omega algebraic | 16-32 | PROVED theorem |

### Phase 5: Integration (Week 5)
**Final verification**

| Agent | Task | Hours | Deliverable |
|-------|------|-------|-------------|
| 5A | Integration & testing | 8-16 | Final build |

---

## Part 5: Agent Instructions Template

```
## STRICT REQUIREMENTS FOR ALL AGENTS

1. You are PROVING a theorem, not axiomatizing it.
2. The keyword "axiom" is FORBIDDEN in your output.
3. The keyword "sorry" is FORBIDDEN in your output.
4. You must provide COMPLETE proofs that compile.

## If You Get Stuck

If a proof seems impossible with current Mathlib:
1. STOP and report the specific blocker
2. Identify what Mathlib API is missing
3. DO NOT convert to axiom as a workaround
4. We will either:
   - Find an alternative proof route
   - Build the missing infrastructure
   - Contribute to Mathlib

## Verification

After completing your task:
1. Run: lake build [YourModule]
2. Run: grep "axiom [your_theorem]" [file]  # Must return nothing
3. Run: grep "sorry" [file]  # Must return nothing on proof track

## Acceptance Criteria
- [ ] File compiles with `lake build`
- [ ] NO axiom keyword for your theorem
- [ ] NO sorry in your proof
- [ ] Proof is mathematically correct
```

---

## Part 6: Estimated Total Effort

| Phase | Tasks | Min Hours | Max Hours |
|-------|-------|-----------|-----------|
| 1 | Differential Forms | 46 | 92 |
| 2 | Cohomology | 8 | 16 |
| 3 | GMT | 64 | 128 |
| 4 | Lefschetz | 40 | 80 |
| 5 | Integration | 8 | 16 |
| **Total** | **11 proofs** | **166 hours** | **332 hours** |

**With 5-10 parallel agents**: 4-8 weeks

---

## Part 7: Risk Mitigation

### Risk: Mathlib Missing Key APIs

**Mitigation**:
1. Identify the specific missing API
2. Check if it can be derived from existing APIs
3. If not, consider:
   - Building it ourselves (add to project)
   - Contributing to Mathlib (longer timeline)
   - Finding alternative proof approach

### Risk: GMT Infrastructure Too Large

**Mitigation**:
1. Identify minimal GMT needed for our specific use
2. Focus on smooth forms on compact Kähler manifolds
3. Use algebraic-geometric approach where possible (Chern classes, etc.)

### Risk: Proof Takes Longer Than Estimated

**Mitigation**:
1. Start with easier tasks to build momentum
2. Parallelize aggressively
3. Regular progress reviews

---

## Appendix A: Verification Commands

```bash
# Full build
lake build Hodge.Kahler.Main

# Check for ANY custom axioms on proof track
echo 'import Hodge.Kahler.Main
#print axioms hodge_conjecture'\'' | lake env lean --stdin

# Expected output (ONLY these 3):
# [propext, Classical.choice, Quot.sound]

# Count all axioms (should be 0 on proof track files)
for f in Hodge/Analytic/Forms.lean Hodge/Cohomology/Basic.lean \
         Hodge/Classical/GAGA.lean Hodge/Classical/CycleClass.lean \
         Hodge/Kahler/Main.lean; do
  echo "=== $f ==="
  grep -c "^axiom" $f || echo "0"
done

# Count all sorry (should be 0 on proof track)
grep -rn "sorry" Hodge/Kahler/Main.lean Hodge/Classical/GAGA.lean \
    Hodge/Analytic/Forms.lean Hodge/Cohomology/Basic.lean
```

---

## Appendix B: What "Proved" Means

A theorem is **proved** if and only if:

1. It compiles without error
2. It does not use `sorry`
3. It does not use any custom `axiom`
4. It only depends on:
   - Mathlib theorems (which are themselves proved)
   - Lean's 3 foundational axioms
   - Other theorems we have proved in this project

Converting a `sorry` to an `axiom` is **NOT proving** - it's just changing the label on an unproven assumption.

---

*Document Version*: 2.0  
*Updated*: January 11, 2026  
*Goal*: ZERO custom axioms, ZERO sorry statements
