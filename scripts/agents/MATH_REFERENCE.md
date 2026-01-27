# Mathematical Reference & Lean Tactics

## 1. Integrability Proofs (for `hausdorffIntegrate_linear`)

To prove `Integrable f μ`, use that `f` is bounded and `μ` is finite.

**Key Lemmas:**
- `MeasureTheory.Measure.lt_top_of_isFiniteMeasure`: finite measure < ⊤
- `MeasureTheory.integrable_of_bounded`: bounded function is integrable
- `Continuous.bounded_on_compact`: continuous function on compact is bounded

**Strategy:**
```lean
-- 1. Show measure is finite
have h_measure : data.measure data.carrier < ⊤ := data.finite_mass

-- 2. Show form is bounded (since X is compact)
have h_bounded : ∃ C, ∀ x, ‖ω.as_alternating x‖ ≤ C := by
  -- SmoothForm implies Continuous, ProjectiveComplexManifold implies CompactSpace
  -- Continuous on compact is bounded
  sorry 

-- 3. Show pairing is bounded
-- |⟨ω, τ⟩| ≤ ‖ω‖ * ‖τ‖. τ is unit. So bounded by C.

-- 4. Apply integrability
-- Bounded * FiniteMeasure → Integrable
```

## 2. Linearity of Integration

Once integrability is established:
```lean
rw [MeasureTheory.set_integral_add, MeasureTheory.set_integral_smul]
· simp only [Complex.add_re, Complex.smul_re]
  rw [mul_comm] -- if needed for c.re * ...
· exact h_integrable_1
· exact h_integrable_2
```

## 3. Stokes' Theorem (Closed Submanifolds)

For `stokes_bound` in `ClosedSubmanifoldData.toIntegrationData`:
- `bdryMass := 0`
- Goal: `|hausdorffIntegrate ... (smoothExtDeriv ω)| ≤ 0`
- This means `∫_Z dω = 0`.

**Proof:**
This follows from Stokes' theorem on a manifold without boundary.
If the infrastructure is missing, you may need to use `sorry` for the fact `∫_Z dω = 0` but *prove* the bound inequality `|0| ≤ 0` using `simp`.

## 4. Mass-Comass Inequality

**Goal:** `|∫_Z ω| ≤ mass(Z) · comass(ω)`

**Proof:**
```lean
rw [hausdorffIntegrate]
-- |(∫ ...).re| ≤ |∫ ...|
apply le_trans (abs_re_le_abs _)
-- |∫ f dμ| ≤ ∫ ‖f‖ dμ
apply le_trans (MeasureTheory.norm_integral_le_integral_norm _)
-- ∫ ‖⟨ω,τ⟩‖ dμ ≤ ∫ comass(ω) dμ
apply MeasureTheory.set_integral_mono
· -- integrability check
  sorry 
· -- bound check: ‖⟨ω,τ⟩‖ ≤ comass(ω)
  intro x hx
  -- definition of comass
  sorry
-- ∫ C dμ = C * μ(S)
rw [MeasureTheory.set_integral_const]
-- = comass(ω) * mass
rfl
```
