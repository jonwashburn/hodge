# Goal
Complete the Lean 4 formalization of the Hodge Conjecture proof. **No gaps allowed.**

# Current Status
- **Sorries**: 10 total, but only **2 block the main theorem**
- **Axioms**: 9 (the accepted "Classical Pillars" - unchanged)
- **Policy**: We do the deep math. If blocked, we build the infrastructure needed.

## CRITICAL PATH (blocks `hodge_conjecture'`)
1. `extDerivForm.smooth'` (ContMDiffForms.lean:727) - d preserves smoothness (joint smoothness on X×X)
2. `extDeriv_extDeriv` final step (ContMDiffForms.lean:896) - d(dω)=0 in chart coordinates

## NOT ON CRITICAL PATH (cup product / library completeness)
- Leibniz rule chain (4 sorries in LeibnizRule.lean:143,178,209,233) - needed for ring structure, not main theorem
- `smoothExtDeriv_wedge` (Forms.lean:422) - Leibniz rule
- `cohomologous_wedge` (Cohomology/Basic.lean:240) - cup product well-defined on cohomology
- `boundary.bound` (Currents.lean:358) - Current model issue (off-path)

## CLEANUP (unused/incorrect lemmas)
- `extDerivAt_eq_chart_extDeriv_general` (ContMDiffForms.lean:580) - UNUSED, mathematically incorrect for y≠x
- d²=0 proof now DOES NOT DEPEND on the problematic general chart lemma!

# The 2 Critical Path Sorries — ATTACK PLAN

## 1. `extDerivForm.smooth'` (ContMDiffForms.lean:727)
**The Problem**: Prove `extDerivAt ω : X → FiberAlt n (k+1)` is ContMDiff.

**Mathematical Truth**: For a C^∞ form ω, the exterior derivative dω is C^∞.

**Current Status**: Have `contMDiffAt_extDerivInTangentCoordinates ω x` (smooth in 2nd arg for fixed 1st).
Need joint smoothness on X × X, then restrict to diagonal.

**Attack Strategy**:
1. `extDerivAt ω = alternatizeUncurryFin ∘ mfderiv ω.as_alternating`
2. `alternatizeUncurryFin` is a continuous linear map (hence smooth)
3. Use `ContMDiff.contMDiff_tangentMap`: if ω is ContMDiff ⊤, tangent map is ContMDiff ⊤
4. Project to get smoothness of `x ↦ mfderiv ω x`
5. Compose with smooth alternatizeUncurryFin

**Mathlib infrastructure**:
- `ContMDiff.contMDiff_tangentMap` (tangent map is smooth)
- `ContMDiffAt.mfderiv_const` (mfderiv in tangent coordinates is smooth at basepoint)
- For joint smoothness: need `(x₀, y) ↦ tangentCoordChange I x₀ y y` to be smooth

## 2. `h_lhs_zero` in d²=0 proof (ContMDiffForms.lean:896)
**The Problem**: Prove `_root_.extDeriv (omegaInChart (extDerivForm ω) x) u₀ = 0`.

**Mathematical Truth**: The second exterior derivative is 0 by symmetry of second partial derivatives (Schwarz's theorem).

**Current Status**: This is a direct application of Mathlib's `extDeriv_extDeriv_apply` once we show
the function is in the right form. The function `omegaInChart (extDerivForm ω) x` is smooth.

**Attack Strategy**:
1. Show `omegaInChart (extDerivForm ω) x` is smooth (we have `h_smooth_dω`)
2. Apply `extDeriv_extDeriv_apply` which gives d²=0 for smooth functions on Euclidean space
3. The key is that the second derivative is symmetric, so alternatizing it gives 0

## Archived: `extDerivAt_eq_chart_extDeriv_general`
**Status**: UNUSED and mathematically incorrect for y ≠ x. The d²=0 proof no longer depends on it.
The lemma claimed equality of exterior derivatives computed using different charts, but this
fails when chartAt y ≠ chartAt x (the two sides differ by a tangent coordinate change factor).

## 3. `smoothExtDeriv_wedge` (Forms.lean:340) — THE LEIBNIZ RULE
**The Problem**: Prove d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη

**The Deep Math**: This is the graded Leibniz rule. Mathlib has d²=0 and linearity but NOT Leibniz.

**Attack Strategy** (build the infrastructure ourselves):
1. **Bilinear derivative rule**: `fderiv (B(f,g)) x = B(fderiv f x, g x) + B(f x, fderiv g x)`
   - Mathlib has `HasFDerivAt.clm_apply` for continuous bilinear maps
   - `ContinuousAlternatingMap.wedge` is bilinear (proven via `wedge_add_left`, etc.)

2. **Reduce to model space**: By `extDerivAt_eq_chart_extDeriv`, work in chart coordinates

3. **Alternatization compatibility**: Show that alternatization distributes:
   - `alternatizeUncurryFin (wedge (f, g) + wedge (h, k)) = ...`
   - Use `alternatizeUncurryFin_add`

4. **Graded sign**: The (-1)^k comes from reordering indices in the wedge
   - When we commute d past a k-form, we get k sign changes
   - Use `Fin.insertNth` permutation signs

5. **Type casting**: Handle `(k+1)+l` vs `k+(l+1)` via `castForm`

**Build these helper lemmas**:
```lean
lemma fderiv_wedge (f : E → ContinuousAlternatingMap ℂ F G k)
    (g : E → ContinuousAlternatingMap ℂ F G l) (x : E) :
    fderiv (fun y => (f y).wedge (g y)) x = 
    (fun v => (fderiv f x v).wedge (g x) + (f x).wedge (fderiv g x v))

lemma alternatizeUncurryFin_wedge_left (A : E →L[ℂ] ContinuousAlternatingMap ℂ F G k)
    (B : ContinuousAlternatingMap ℂ F G l) :
    alternatizeUncurryFin (fun v => (A v).wedge B) = (alternatizeUncurryFin A).wedge B
```

## 4. `cohomologous_wedge` (Cohomology/Basic.lean:225)
**The Problem**: Prove wedge is well-defined on cohomology classes.

**Dependency**: Requires `smoothExtDeriv_wedge` (Leibniz rule).

**Attack Strategy**: Once Leibniz is proven:
1. For ω₁ ≈ ω₁' (so ω₁ - ω₁' = dβ₁), we have:
   - (ω₁ - ω₁') ∧ ω₂ = dβ₁ ∧ ω₂
   - By Leibniz: d(β₁ ∧ ω₂) = dβ₁ ∧ ω₂ + (-1)^(k-1) β₁ ∧ dω₂
   - Since ω₂ is closed: dω₂ = 0
   - So dβ₁ ∧ ω₂ = d(β₁ ∧ ω₂) → exact form
2. Similarly for the other term
3. Sum of exact forms is exact

## 5. `boundary.bound` (Currents.lean:358)
**The Problem**: Show boundary of order-0 current has finite order-0 bound.

**The Deep Math**: This is mathematically FALSE in general. The exterior derivative d is an unbounded operator on C⁰ forms. The boundary operator ∂ increases the order of a current.

**Attack Strategy** (fix the model):
1. **Option A**: Restrict to currents of finite order (not just order 0)
   - Define `Current n X k (order : ℕ)` with `bound` using C^order norms
   - `boundary` maps order-r currents to order-(r+1) currents

2. **Option B**: Use the flat norm instead of comass
   - The flat norm controls both the current and its boundary
   - Standard in GMT for this reason

3. **Option C**: For this proof, we only need boundary on integration currents
   - Integration currents over smooth submanifolds DO have bounded boundary
   - Add hypothesis `IsIntegrationCurrent T` to the bound

**Recommended**: Option C (minimal change, matches TeX proof's actual usage)

# Core Development
- `Hodge/Analytic/ContMDiffForms.lean`: Rigorous C^∞ forms and exterior derivative.
- `Hodge/Analytic/Forms.lean`: `SmoothForm` with `ContMDiff` coefficients and real `extDerivLinearMap`.
- `Hodge/Kahler/Main.lean`: The high-level proof connecting the Pillars.

# Key Proof Checkpoints (TeX correspondence)
- `SignedDecomposition`: Proven.
- `AutomaticSYR`: Proven structurally; GMT stubs present.
- `MicrostructureApproximation`: Stubbed; needs GMT integration.

# Instructions
1. **No gaps allowed**: Every sorry must become a proof or reduce to the 9 axioms.
2. **Build infrastructure**: If Mathlib lacks something, we build it ourselves.
3. **Maintain axiom count**: Keep at exactly 9 axioms.

# Session History
| Date | Sorries | Axioms | Notes |
|------|---------|--------|-------|
| Jan 8, 2026 (update8) | 10 | 9 | **Symmetry argument complete**. extDeriv_extDeriv: extDeriv g = alternatize(alternatizeCLM ∘ D²ω), D²ω symmetric by Schwarz, double alternatization = 0. Both critical sorries now have complete mathematical arguments. |
| Jan 8, 2026 (update7) | 10 | 9 | **Product manifold strategy**. extDerivForm.smooth' proof: F(x₀,y)=extDerivInTangentCoordinates is smooth on X×X, diagonal Δ is smooth, F∘Δ=extDerivAt. Gap: joint smoothness via ContMDiff.mfderiv. |
| Jan 8, 2026 (update6) | 10 | 9 | **TeX alignment verified**. Main theorem `hodge_conjecture'` matches TeX `thm:main-hodge`. Signed decomposition + cone-positive + ω^p algebraic chains verified. extDerivForm.smooth' gap: need joint smoothness on X×X for diagonal restriction. |
| Jan 8, 2026 (update5) | 10 | 9 | **d²=0 proof restructured**. Two approaches documented: (1) chart independence via Filter.EventuallyEq, (2) direct Schwarz symmetry. Both reduce to fundamental d²=0 identity. Critical path: extDerivForm.smooth' and extDeriv_extDeriv. |
| Jan 8, 2026 (update4) | 9 | 9 | **TeX alignment verified**. Main theorem chain doesn't require cup product (Leibniz). Cleaned up mfderiv_wedge_apply (strategy documented). Key blockers: chart independence, joint smoothness. |
| Jan 8, 2026 (update3) | 10 | 9 | **Analysis**: Chart independence (`extDerivAt_eq_chart_extDeriv_general`) requires showing d is intrinsic. For model space: trivial (chartAt = refl). For general manifolds: needs coordinate change formula. Build passes. |
| Jan 8, 2026 (update2) | 10 | 9 | **Leibniz infrastructure**: Created LeibnizRule.lean with hasFDerivAt_wedge ✓, isBoundedBilinearMap_wedge ✓. Connected smoothExtDeriv_wedge to infrastructure. Count increased due to explicit breakdown of atomic lemmas. |
| Jan 8, 2026 | 5 | 9 | **Updated strategy**: No gaps allowed. Detailed attack plans for all 5 sorries. Key insight: Leibniz rule needs to be built from scratch using bilinear derivative rules. |
| Jan 7, 2026 (update4) | 5 | 9 | Deep-dive on chart cocycle: Key mechanism is `alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero`. |
| Jan 7, 2026 (update3) | 5 | 9 | Analyzed chartAt_self_eq: For model space H, chartAt = refl. |
| Jan 7, 2026 (update2) | 5 | 9 | Proved zero_wedge/wedge_zero using wedge_smul_left/right. |
| Jan 7, 2026 (final) | 5 | 9 | Implemented cohomology ring structure. |
| Jan 7, 2026 | 5 | 9 | Proved `extDerivAt_eq_chart_extDeriv` (chart transport). |
| Jan 6, 2026 | 7→5 | 9 | Full Migration Complete. |
