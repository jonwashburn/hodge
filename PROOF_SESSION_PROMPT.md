# Goal
Complete the Lean 4 formalization of the Hodge Conjecture proof. **No gaps allowed.**

# Current Status
- **Sorries**: 5 (must be eliminated - see attack plan below)
- **Axioms**: 9 (the accepted "Classical Pillars" - unchanged)
- **Policy**: We do the deep math. If blocked, we build the infrastructure needed.

# The 5 Remaining Sorries — ATTACK PLAN

## 1. `extDerivAt_eq_chart_extDeriv_general` (ContMDiffForms.lean:522)
**The Problem**: Prove chart independence of exterior derivative. Need:
```lean
fderiv (ω ∘ (chartAt y).symm) ((chartAt y) y) = fderiv (ω ∘ (chartAt x).symm) ((chartAt x) y)
```

**The Deep Math**: By chain rule with τ = (chartAt x) ∘ (chartAt y).symm:
- LHS = RHS ∘ fderiv τ ((chartAt y) y)
- Need: `fderiv τ ((chartAt y) y) = id`

**Attack Strategy**:
1. Use Mathlib's `tangentCoordChange_def`: `tangentCoordChange I x y z = fderivWithin (extChartAt y ∘ (extChartAt x).symm) (range I) (extChartAt x z)`
2. For `modelWithCornersSelf`, `range I = univ` so `fderivWithin = fderiv`
3. Key: `tangentCoordChange I y x y = fderiv ((chartAt x) ∘ (chartAt y).symm) ((chartAt y) y)`
4. Use `hasFDerivWithinAt_tangentCoordChange` to extract the derivative
5. The inverse `tangentCoordChange I x y y` cancels it to give identity

**Mathlib lemmas to use**:
- `tangentCoordChange_def`, `hasFDerivWithinAt_tangentCoordChange`
- `tangentCoordChange_comp` (composition law)
- For model space: `extChartAt_model_space_eq_id`

## 2. `extDerivForm.smooth'` (ContMDiffForms.lean:625)
**The Problem**: Prove `extDerivAt ω : X → FiberAlt n (k+1)` is ContMDiff.

**The Deep Math**: Joint smoothness on X × X then restrict to diagonal.
- Have: `contMDiffAt_extDerivInTangentCoordinates ω x₀` (smooth in 2nd arg for fixed 1st)
- Need: `(x₀, y) ↦ extDerivInTangentCoordinates ω x₀ y` jointly smooth

**Attack Strategy**:
1. Define `F : X × X → FiberAlt n (k+1)` by `F(x₀, y) = extDerivInTangentCoordinates ω x₀ y`
2. Use product manifold structure: show ContMDiff on X × X
3. The diagonal Δ : X → X × X, x ↦ (x,x) is smooth (`contMDiff_id.prodMk contMDiff_id`)
4. By `extDerivInTangentCoordinates_diag`, `extDerivAt ω = F ∘ Δ`
5. Composition of smooth maps is smooth

**Key infrastructure**: Need to prove F is jointly smooth. Use:
- `ContMDiff.comp` for function composition
- The explicit formula for `extDerivInTangentCoordinates` involves smooth maps
- `mfderiv` varies smoothly in tangent coordinates (`ContMDiffAt.mfderiv_const`)

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
| Jan 8, 2026 (update2) | 10 | 9 | **Leibniz infrastructure**: Created LeibnizRule.lean with hasFDerivAt_wedge ✓, isBoundedBilinearMap_wedge ✓. Connected smoothExtDeriv_wedge to infrastructure. Count increased due to explicit breakdown of atomic lemmas. |
| Jan 8, 2026 | 5 | 9 | **Updated strategy**: No gaps allowed. Detailed attack plans for all 5 sorries. Key insight: Leibniz rule needs to be built from scratch using bilinear derivative rules. |
| Jan 7, 2026 (update4) | 5 | 9 | Deep-dive on chart cocycle: Key mechanism is `alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero`. |
| Jan 7, 2026 (update3) | 5 | 9 | Analyzed chartAt_self_eq: For model space H, chartAt = refl. |
| Jan 7, 2026 (update2) | 5 | 9 | Proved zero_wedge/wedge_zero using wedge_smul_left/right. |
| Jan 7, 2026 (final) | 5 | 9 | Implemented cohomology ring structure. |
| Jan 7, 2026 | 5 | 9 | Proved `extDerivAt_eq_chart_extDeriv` (chart transport). |
| Jan 6, 2026 | 7→5 | 9 | Full Migration Complete. |
