# Mathematical Reference for Lean Agents

This document extracts key proofs from the paper `JA_hodge_approach_clean_black_FINAL.tex` to guide Lean formalization.

---

## 1. Mass-Comass Inequality

**From paper (Definition 6.1, line 584-588):**

The **comass** of a k-form η is:
```
‖η‖_comass := sup_{x∈X} sup{ |η_x(v₁,...,vₖ)| : v₁∧...∧vₖ is unit simple k-vector }
```

The **mass** of a k-current T is:
```
Mass(T) := sup{ ⟨T,η⟩ : η smooth k-form, ‖η‖_comass ≤ 1 }
```

**Key inequality:**
```
|⟨T, η⟩| ≤ Mass(T) · ‖η‖_comass
```

**For integration currents [Z]:**
```
|∫_Z ω| ≤ Mass(Z) · comass(ω)
```

**Proof sketch:**
1. By definition of comass: |ω_x(τ_x)| ≤ comass(ω) for unit τ
2. Integration: |∫_Z ω| = |∫_Z ⟨ω(x), τ(x)⟩ dH^k| ≤ ∫_Z |⟨ω, τ⟩| dH^k
3. Bound: ≤ ∫_Z comass(ω) dH^k = comass(ω) · H^k(Z) = comass(ω) · Mass(Z)

---

## 2. Flat Limits of Cycles are Cycles

**From paper (Lemma, line 2274-2287):**

> **Lemma (Flat limits of cycles are cycles):**
> Let T_k be integral currents with ∂T_k = 0 and sup_k Mass(T_k) < ∞.
> Assume T_k → T in flat norm. Then T is an integral cycle (∂T = 0).

**Proof:**
1. The boundary operator ∂ is continuous with respect to flat convergence
2. Hence ∂T_k → ∂T in flat norm
3. Since ∂T_k = 0 for all k, we get ∂T = 0
4. T is integral by closure under flat convergence with uniform mass and boundary mass

**Key fact for Lean:** The boundary operator is a continuous linear map in the flat topology.

---

## 3. Stokes' Theorem for Currents

**For closed submanifolds (∂Z = ∅):**
```
∫_Z dω = ∫_∂Z ω = 0
```

**For rectifiable sets with boundary:**
```
∫_Z dω = ∫_∂Z ω
```

Hence the Stokes bound:
```
|∫_Z dω| = |∫_∂Z ω| ≤ Mass(∂Z) · comass(ω)
```

**From paper (line 4216):**
> Apply Stokes to each S_Q and sum over Q. Each interior face F=Q∩Q' 
> occurs twice with opposite orientations.

---

## 4. Federer-Fleming Compactness

**From paper (line 2330-2335):**

> **Federer-Fleming compactness** applies to integral currents on a compact 
> Riemannian manifold once sup_k(Mass(T_k) + Mass(∂T_k)) < ∞.

**Statement:** If T_k are integral currents with uniformly bounded mass and boundary mass, then a subsequence converges in flat norm to an integral current T.

**Reference:** Federer [4.2.17]

---

## 5. Harvey-Lawson Structure Theorem

**From paper (line 8757):**

> By the Harvey-Lawson structure theorem [HL82, Thm 4.2]:
> Since T is an integral ψ-calibrated cycle where ψ is the Wirtinger calibration,
> T is a positive holomorphic (n-p)-cycle.

**Key fact:** Integral currents calibrated by the Wirtinger form are holomorphic subvarieties.

---

## 6. Integration Linearity (Bochner Integral)

For the Bochner integral on a measure space:
```
∫ (c·f + g) dμ = c · ∫f dμ + ∫g dμ
```

**Key Mathlib lemmas:**
- `MeasureTheory.integral_add` - integral of sum
- `MeasureTheory.integral_smul` - scalar multiple
- `MeasureTheory.integral_add_measure` - over sum of measures

**For hausdorffIntegrate:**
```lean
hausdorffIntegrate data (c • ω₁ + ω₂) = c * hausdorffIntegrate data ω₁ + hausdorffIntegrate data ω₂
```

**Proof needs:**
1. Show integrand is integrable (bounded continuous on compact set)
2. Apply integral_add and integral_smul
3. Use Complex.add_re and that c : ℝ (so c.re = c)

---

## 7. Key Mathlib Lemmas to Use

### For integral linearity:
- `MeasureTheory.integral_add`: `∫ (f + g) = ∫ f + ∫ g`
- `MeasureTheory.integral_smul`: `∫ (c • f) = c • ∫ f`
- `MeasureTheory.Integrable.add`: integrability of sum
- `MeasureTheory.Integrable.smul`: integrability under scaling

### For bounds:
- `MeasureTheory.norm_integral_le_integral_norm`: `‖∫ f‖ ≤ ∫ ‖f‖`
- `abs_re_le_abs`: `|z.re| ≤ |z|` for z : ℂ

### For boundary continuity:
- The boundary operator ∂ : Current → Current should be continuous in flat norm
- This is built into the definition of flat norm convergence

---

## 8. Specific Sorry Proofs

### hausdorffIntegrate_linear (Currents.lean:692)
```lean
theorem hausdorffIntegrate_linear ... :
    hausdorffIntegrate data (c • ω₁ + ω₂) = c * hausdorffIntegrate data ω₁ + hausdorffIntegrate data ω₂ := by
  -- Goal: (∫ x, (c • f(x) + g(x)) dμ).re = c * (∫ x, f(x) dμ).re + (∫ x, g(x) dμ).re
  -- 1. Use linearity of alternating map evaluation
  simp only [hausdorffIntegrate, formVectorPairing]
  simp only [SmoothForm.add_apply, SmoothForm.smul_real_apply]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply]
  -- 2. Now: (∫ x, c • f(x) + g(x) dμ).re
  -- 3. Use MeasureTheory.set_integral_add and set_integral_smul
  -- 4. Use Complex.add_re and Real.smul_re
  sorry -- Need: integrability + Mathlib lemmas
```

### hausdorffIntegrate_bound (Currents.lean:708)
```lean
theorem hausdorffIntegrate_bound ... :
    |hausdorffIntegrate data ω| ≤ data.mass * comass ω := by
  -- Goal: |∫_Z ω| ≤ Mass(Z) · comass(ω)
  -- 1. |hausdorffIntegrate| = |(∫ x, ⟨ω,τ⟩ dμ).re|
  -- 2. ≤ |∫ x, ⟨ω,τ⟩ dμ| by abs_re_le_abs
  -- 3. ≤ ∫ x, |⟨ω,τ⟩| dμ by norm_integral_le_integral_norm
  -- 4. ≤ ∫ x, comass(ω) dμ by definition of comass
  -- 5. = comass(ω) · μ(carrier) = comass(ω) · mass
  sorry -- Need: comass bound on pairing
```

### stokes_bound closed (Currents.lean:905)
```lean
-- For closed submanifolds: ∂Z = ∅, so bdryMass = 0
-- Goal: |∫_Z dω| ≤ 0 * comass(dω) = 0
-- This requires showing ∫_Z dω = 0 for closed Z (Stokes)
```

---

## Summary

The paper provides all the mathematical content. The Lean formalization needs to:

1. **Connect to Mathlib** - Use existing lemmas for Bochner integral, norms
2. **Build small steps** - Prove helper lemmas first
3. **Use the definitions correctly** - hausdorffIntegrate, mass, comass are already defined
4. **Apply the mathematical facts** - The proofs are in the paper!
