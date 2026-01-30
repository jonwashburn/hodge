# CRITICAL AGENT CONTEXT (Updated 2026-01-30)

This repo is a Lean 4 formalization of the Hodge conjecture. The proof track is **green** and the
remaining “deep content” is isolated behind explicit placeholders (sorries/axioms/typeclasses).

## 0. Build rule (repo-specific)

**Before any `lake build`, run:**

```bash
lake exe cache get
```

## 1. Phase‑1 functional-analytic layer (DO NOT fight it)

### 1.1 `SmoothForm` is NOT discrete anymore

`SmoothForm n X k` now carries a genuine seminormed/Normed structure over ℝ coming from comass:

- **File**: `Hodge/Analytic/Norms.lean`
- **Key fact**: `‖ω‖ = comass ω` (and comass triangle/scaling lemmas are proved)

**Do NOT use** `continuous_of_discreteTopology`. Any old proofs relying on “everything is continuous”
will now break and must be replaced with bounded-linear-map arguments.

### 1.2 `Current` is a continuous linear functional (`→L[ℝ]`)

`Current n X k` is now:

- **File**: `Hodge/Analytic/Currents.lean`
- **Definition**:
  - `toFun : SmoothForm n X k →L[ℝ] ℝ`
  - `boundary_bound : (k = 0 → True) ∧ (k = k'+1 → ∃ M, ∀ ω, |T(dω)| ≤ M * ‖ω‖)`

**Important consequences**

- **No per-current boundedness field** anymore. Use operator norm:
  - Pattern: `simpa [Real.norm_eq_abs] using (T.toFun.le_opNorm ω)`
- `d` (here `smoothExtDeriv`) is **not** continuous for comass; we therefore keep `boundary_bound`
  as a separate hypothesis.

### 1.3 `Current.boundary` is built from `boundary_bound` (not by continuity of `d`)

- `Current.boundary` is constructed via `LinearMap.mkContinuousOfExistsBound`.
- There is a simp lemma:
  - `Current.boundary_toFun`

## 2. “Still placeholder” items (real remaining axioms / stubs)

Full scan (`./scripts/audit_stubs.sh --full`) currently reports these **axioms**:

- `Hodge/Classical/GAGA.lean`:
  - `axiom fundamental_eq_representing_axiom` (spine bridge; deep geometry/cohomology)
- `Hodge/Analytic/Integration/SubmanifoldIntegral.lean`:
  - `opaque submanifoldIntegral ... : ℂ`
  - `axiom integral_add`, `axiom integral_smul`, `axiom integral_continuous`
- Legacy “Stage‑1 test forms” namespace `Hodge.TestForms` (mostly off the main proof track):
  - `Hodge/Analytic/TestForms/LFTopology.lean`: `axiom realTopology`
  - `Hodge/Analytic/TestForms/Operations.lean`: `axiom leibniz`, `axiom pullback_d`

## 3. Remaining `sorry` locations (current repo)

`./scripts/audit_stubs.sh --full` currently reports:

- `Hodge/Kahler/Main.lean`:
  - one `sorry` in the “defect → 0” portion (deep calibration/microstructure content)
- `Hodge/Analytic/FlatNormReal.lean`:
  - many sorries (generic RealChain development; typically **off-track**)
- `Hodge/Analytic/Stage2/IntegrationCurrentsManifoldSkeleton.lean`:
  - several `Prop := sorry` placeholders + one remaining `sorry` used for mass computation
- plus a quarantined file under `Hodge/Quarantine/...` (off-track)

## 4. What the “proof track” currently depends on

Ground truth is Lean’s kernel report:

```lean
#print axioms hodge_conjecture
#print axioms hodge_conjecture'
```

Currently:

- `hodge_conjecture` depends on `[propext, Classical.choice, Quot.sound]`
- `hodge_conjecture'` depends on `[propext, Classical.choice, Quot.sound]`

So: **no `sorryAx` in the dependency cone** of the main theorem.

## 5. What NOT to do (hard rules)

- **Never** use `admit`.
- **Never** replace nontrivial goals with trivializations (`:= trivial`, `:= True`, `⟨⟩`, etc).
- Do **not** reintroduce the “SmoothForm is discrete topology” hack.
- If you touch anything in the functional-analytic layer:
  - keep `SmoothForm` seminormed by comass
  - keep `Current` as `→L[ℝ]` with only `boundary_bound` stored

## 6. High-signal proof patterns (use these)

- **Bounded linear ⇒ continuous**:

```lean
-- Given f : E →ₗ[ℝ] F and ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖
exact f.mkContinuousOfExistsBound hbound
```

- **Current boundedness via opNorm**:

```lean
-- |T(ω)| ≤ ‖T‖ * ‖ω‖
simpa [Real.norm_eq_abs] using (T.toFun.le_opNorm ω)
```

## 7. Where to focus agent effort

If you are running autonomous agents, prioritize:

1. `Hodge/Kahler/Main.lean` (the remaining `sorry` — deep calibration defect = 0)
2. Then, if explicitly requested: eliminate the explicit axioms in Submanifold integration / spine bridge.

