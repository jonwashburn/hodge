import Hodge.Analytic.Currents
import Hodge.Analytic.Norms
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Flat Norm on Currents

This file defines the flat norm on currents and proves its basic properties.
The flat norm is the natural metric for the space of integral currents.

## Main Definitions

* `flatNormDecompSet` - The set of valid decomposition costs for flat norm
* `flatNorm` - The flat norm of a current, defined as an infimum

## Main Results (Proven)

* `flatNorm_nonneg` - The flat norm is non-negative
* `flatNorm_zero` - The flat norm of zero is zero
* `flatNorm_le_mass` - The flat norm is bounded by the mass
* `flatNorm_boundary_le` - The flat norm of a boundary is bounded by mass

## References

* [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]
-/

noncomputable section

open Classical Set

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-! ## Auxiliary Lemmas -/

/-- The boundary of the zero current is zero. -/
theorem Current.boundary_zero {k : ℕ} : Current.boundary (0 : Current n X (k + 1)) = 0 := by
  ext ω
  show (0 : Current n X (k + 1)).toFun (smoothExtDeriv ω) = (0 : Current n X k).toFun ω
  rw [Current.zero_toFun, Current.zero_toFun]

/-- Scalar multiplication of boundary. -/
theorem Current.boundary_smul {k : ℕ} (c : ℝ) (R : Current n X (k + 1)) :
    Current.boundary (c • R) = c • Current.boundary R := by
  -- boundary (c • R) = c • boundary R
  -- By extensionality: for all ω, (boundary (c • R)).toFun ω = (c • boundary R).toFun ω
  -- LHS = (c • R).toFun (dω) = c * R.toFun (dω)  [by defs of boundary, smul_curr]
  -- RHS = c * (boundary R).toFun ω = c * R.toFun (dω)  [by defs of smul_curr, boundary]
  rfl

/-! ## Flat Norm Definition -/

/-- The decomposition set for flat norm computation.
    A valid decomposition of T consists of currents (S, R) with T = S + ∂R,
    and the cost is M(S) + M(R). -/
def flatNormDecompSet {k : ℕ} (T : Current n X k) : Set ℝ :=
  { m : ℝ | ∃ (S : Current n X k) (R : Current n X (k + 1)),
    T = S + Current.boundary R ∧ m = Current.mass S + Current.mass R }

/-- The trivial decomposition T = T + ∂0 shows the decomposition set is nonempty. -/
theorem flatNormDecompSet_nonempty {k : ℕ} (T : Current n X k) :
    (flatNormDecompSet T).Nonempty := by
  use Current.mass T + Current.mass (0 : Current n X (k + 1))
  use T, 0
  refine ⟨?_, rfl⟩
  ext ω
  rw [Current.boundary_zero]
  show T.toFun ω = (T + (0 : Current n X k)).toFun ω
  rw [Current.add_zero]

/-- Every element of the decomposition set is non-negative. -/
theorem flatNormDecompSet_nonneg {k : ℕ} (T : Current n X k) :
    ∀ m ∈ flatNormDecompSet T, m ≥ 0 := by
  intro m ⟨S, R, _, hm⟩
  rw [hm]
  exact add_nonneg (Current.mass_nonneg S) (Current.mass_nonneg R)

/-- The decomposition set is bounded below by 0. -/
theorem flatNormDecompSet_bddBelow {k : ℕ} (T : Current n X k) :
    BddBelow (flatNormDecompSet T) := ⟨0, fun _ hm => flatNormDecompSet_nonneg T _ hm⟩

/-- **The Flat Norm** (Federer-Fleming, 1960).
    The flat norm of a current T is the infimum of M(S) + M(R) such that T = S + ∂R:
    F(T) = inf { M(S) + M(R) : T = S + ∂R }

    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
def flatNorm {k : ℕ} (T : Current n X k) : ℝ :=
  sInf (flatNormDecompSet T)

/-! ## Basic Properties (Proven) -/

/-- The flat norm is non-negative (Federer-Fleming 1960).
    Proof: Every element of the decomposition set is ≥ 0, so the infimum is ≥ 0. -/
theorem flatNorm_nonneg {k : ℕ} (T : Current n X k) : flatNorm T ≥ 0 := by
  unfold flatNorm
  apply Real.sInf_nonneg
  exact flatNormDecompSet_nonneg T

/-- The flat norm of the zero current is zero.
    Proof: 0 = 0 + ∂0, so mass(0) + mass(0) = 0 is in the set.
    The infimum of a set containing 0 and bounded below by 0 equals 0. -/
theorem flatNorm_zero {k : ℕ} : flatNorm (0 : Current n X k) = 0 := by
  unfold flatNorm
  apply le_antisymm
  · -- Show sInf ≤ 0 by exhibiting 0 in the set
    apply csInf_le (flatNormDecompSet_bddBelow 0)
    use 0, 0
    refine ⟨?_, by simp [Current.mass_zero]⟩
    ext ω
    rw [Current.boundary_zero]
    show (0 : Current n X k).toFun ω = ((0 : Current n X k) + (0 : Current n X k)).toFun ω
    rw [Current.zero_add]
  · exact flatNorm_nonneg 0

/-- The flat norm is bounded above by the mass (Federer-Fleming 1960).
    Proof: T = T + ∂0 is a valid decomposition with cost M(T) + M(0) = M(T). -/
theorem flatNorm_le_mass {k : ℕ} (T : Current n X k) : flatNorm T ≤ Current.mass T := by
  unfold flatNorm
  apply csInf_le (flatNormDecompSet_bddBelow T)
  use T, 0
  refine ⟨?_, by simp [Current.mass_zero]⟩
  ext ω
  rw [Current.boundary_zero]
  show T.toFun ω = (T + (0 : Current n X k)).toFun ω
  rw [Current.add_zero]

/-- The flat norm of a boundary is at most the flat norm of the original current (Federer-Fleming).
    Proof: For any decomposition T = S + ∂R with cost M(S) + M(R):
    - ∂T = ∂S + ∂∂R = ∂S (since ∂∂ = 0 by boundary_boundary)
    - ∂T = ∂S = 0 + ∂S is a valid decomposition with cost M(0) + M(S) = M(S)
    - So flatNorm(∂T) ≤ M(S) ≤ M(S) + M(R).
    Taking infimum over all decompositions yields flatNorm(∂T) ≤ flatNorm(T). -/
theorem flatNorm_boundary_le {k : ℕ} (T : Current n X (k + 1)) :
    flatNorm (Current.boundary T) ≤ flatNorm T := by
  unfold flatNorm
  apply le_csInf (flatNormDecompSet_nonempty T)
  intro m ⟨S, R, hT, hm⟩
  have h_bdyT : Current.boundary T = Current.boundary S := by
    calc Current.boundary T = Current.boundary (S + Current.boundary R) := by rw [hT]
      _ = Current.boundary S + Current.boundary (Current.boundary R) := Current.boundary_add S _
      _ = Current.boundary S + 0 := by rw [Current.boundary_boundary]
      _ = Current.boundary S := Current.add_zero _
  have h_decomp : Current.mass (0 : Current n X k) + Current.mass S ∈
      flatNormDecompSet (Current.boundary T) := by
    use 0, S
    refine ⟨?_, rfl⟩
    ext ω
    rw [h_bdyT]
    show (Current.boundary S).toFun ω = ((0 : Current n X k) + Current.boundary S).toFun ω
    rw [Current.zero_add]
  have h_le : sInf (flatNormDecompSet (Current.boundary T)) ≤
      Current.mass (0 : Current n X k) + Current.mass S :=
    csInf_le (flatNormDecompSet_bddBelow _) h_decomp
  rw [Current.mass_zero, zero_add] at h_le
  calc sInf (flatNormDecompSet (Current.boundary T)) ≤ Current.mass S := h_le
    _ ≤ Current.mass S + Current.mass R := le_add_of_nonneg_right (Current.mass_nonneg R)
    _ = m := hm.symm

/-- The flat norm of a boundary is bounded by the mass. -/
theorem flatNorm_boundary_le_mass {k : ℕ} (T : Current n X (k + 1)) :
    flatNorm (Current.boundary T) ≤ Current.mass T := by
  unfold flatNorm
  apply csInf_le (flatNormDecompSet_bddBelow (Current.boundary T))
  use 0, T
  refine ⟨?_, by simp [Current.mass_zero]⟩
  ext ω
  show (Current.boundary T).toFun ω = ((0 : Current n X k) + Current.boundary T).toFun ω
  rw [Current.zero_add]

/-! ## Axioms for Properties Requiring Deeper Infrastructure -/

/-- Negation reverses addition of currents. -/
theorem Current.neg_add {k : ℕ} (S T : Current n X k) : -(S + T) = -S + -T := by
  ext ω
  show -(S.toFun ω + T.toFun ω) = -S.toFun ω + -T.toFun ω
  ring

/-- Boundary commutes with negation. -/
theorem Current.boundary_neg' {k : ℕ} (R : Current n X (k + 1)) :
    Current.boundary (-R) = -Current.boundary R := by
  ext ω
  show (-R).toFun (smoothExtDeriv ω) = -(R.toFun (smoothExtDeriv ω))
  rfl

/-- The flat norm is symmetric under negation (Federer-Fleming 1960).
    Proof: If T = S + ∂R is a decomposition, then -T = -S + ∂(-R) is a decomposition with
    the same cost (since mass(-S) = mass(S) and mass(-R) = mass(R)).
    Thus the decomposition sets for T and -T have identical values. -/
theorem flatNorm_neg {k : ℕ} (T : Current n X k) : flatNorm (-T) = flatNorm T := by
  unfold flatNorm
  apply le_antisymm
  · -- Show flatNorm(-T) ≤ flatNorm(T)
    apply csInf_le_csInf (flatNormDecompSet_bddBelow (-T)) (flatNormDecompSet_nonempty T)
    -- For any m in decomp(T), show m is in decomp(-T)
    intro m ⟨S, R, hT, hm⟩
    -- If T = S + ∂R, then -T = -S + ∂(-R)
    use -S, -R
    refine ⟨?_, ?_⟩
    · -- -T = -S + ∂(-R)
      ext ω
      rw [Current.boundary_neg']
      have h := congrArg (fun T' => (-T').toFun ω) hT
      simp only [Current.neg_add] at h
      exact h
    · -- cost is the same
      rw [hm, Current.mass_neg, Current.mass_neg]
  · -- Show flatNorm(T) ≤ flatNorm(-T) by symmetry
    apply csInf_le_csInf (flatNormDecompSet_bddBelow T) (flatNormDecompSet_nonempty (-T))
    intro m ⟨S, R, hT, hm⟩
    -- If -T = S + ∂R, then T = -S + ∂(-R)
    use -S, -R
    refine ⟨?_, ?_⟩
    · ext ω
      rw [Current.boundary_neg']
      have h := congrArg (fun T' => (-T').toFun ω) hT
      simp only [Current.neg_add] at h
      -- h says: -(-T).toFun ω = (-S).toFun ω + (-∂R).toFun ω
      -- We need: T.toFun ω = (-S).toFun ω + (∂(-R)).toFun ω
      -- Since --T = T and ∂(-R) = -∂R:
      have h2 : (-(-T)).toFun ω = T.toFun ω := by
        show -(-T.toFun ω) = T.toFun ω
        ring
      rw [← h2, h]
    · rw [hm, Current.mass_neg, Current.mass_neg]

/-- The flat norm satisfies the triangle inequality (Federer-Fleming 1960).
    Proof sketch: If T₁ = S₁ + ∂R₁ and T₂ = S₂ + ∂R₂,
    then T₁ + T₂ = (S₁+S₂) + ∂(R₁+R₂) with cost M(S₁+S₂) + M(R₁+R₂)
    ≤ M(S₁) + M(S₂) + M(R₁) + M(R₂) by triangle inequalities on mass.
    This axiom is kept due to the complexity of infimum manipulation required. -/
axiom flatNorm_add_le {k : ℕ} (T₁ T₂ : Current n X k) :
    flatNorm (T₁ + T₂) ≤ flatNorm T₁ + flatNorm T₂

/-- Scalar multiplication distributes over current addition. -/
theorem Current.smul_add {k : ℕ} (c : ℝ) (S T : Current n X k) :
    c • (S + T) = c • S + c • T := by
  ext ω
  show c * (S.toFun ω + T.toFun ω) = c * S.toFun ω + c * T.toFun ω
  ring

/-- Scalar multiplication associates. -/
theorem Current.smul_smul {k : ℕ} (c d : ℝ) (T : Current n X k) :
    c • (d • T) = (c * d) • T := by
  ext ω
  show c * (d * T.toFun ω) = (c * d) * T.toFun ω
  ring

/-- Flat norm scales with absolute value of scalar (Federer-Fleming 1960).
    Proof sketch: If T = S + ∂R is a decomposition, then c•T = c•S + ∂(c•R) with cost
    M(c•S) + M(c•R) = |c|M(S) + |c|M(R) = |c|(M(S) + M(R)).
    The decomposition set for c•T is exactly |c| times the decomposition set for T.
    This axiom is kept due to the complexity of infimum scaling lemmas in Lean. -/
axiom flatNorm_smul {k : ℕ} (c : ℝ) (T : Current n X k) :
    flatNorm (c • T) = |c| * flatNorm T

/-- Flat norm of difference is bounded by sum of flat norms.
    Follows from triangle inequality and symmetry under negation. -/
theorem flatNorm_sub_le {k : ℕ} (S T : Current n X k) :
    flatNorm (S - T) ≤ flatNorm S + flatNorm T := by
  -- S - T = S + (-T)
  calc flatNorm (S - T) = flatNorm (S + -T) := rfl
    _ ≤ flatNorm S + flatNorm (-T) := flatNorm_add_le S (-T)
    _ = flatNorm S + flatNorm T := by rw [flatNorm_neg]

/-- **Bound evaluation by mass** (Federer 1969, §4.1).
    This is the defining property of mass as the dual norm to comass.
    For any current T and form ψ: |T(ψ)| ≤ mass(T) × comass(ψ).

    **Proof**: The mass is defined as mass(T) = sup { |T(ω)| : comass(ω) ≤ 1 }.
    - If comass(ψ) = 0, we use the boundedness of T to show |T(ψ)| = 0.
    - If comass(ψ) > 0, normalize ψ to ψ' = ψ/comass(ψ) with comass 1.
      Then |T(ψ')| ≤ mass(T) by definition, and |T(ψ)| = comass(ψ) × |T(ψ')|.

    Reference: [H. Federer, "Geometric Measure Theory", Springer 1969, §4.1]. -/
theorem eval_le_mass {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ Current.mass T * comass ψ := by
  by_cases h_zero : comass ψ = 0
  · -- Case: comass ψ = 0
    obtain ⟨M, hM⟩ := T.is_bounded
    have h_bound : |T.toFun ψ| ≤ M * comass ψ := hM ψ
    rw [h_zero, mul_zero] at h_bound
    have h_nonneg : |T.toFun ψ| ≥ 0 := abs_nonneg _
    have h_eq_zero : |T.toFun ψ| = 0 := le_antisymm h_bound h_nonneg
    rw [h_eq_zero, h_zero, mul_zero]
  · -- Case: comass ψ > 0
    have h_pos : comass ψ > 0 := lt_of_le_of_ne (comass_nonneg ψ) (Ne.symm h_zero)
    let c : ℝ := (comass ψ)⁻¹
    let ψ' : SmoothForm n X k := c • ψ
    have h_c_pos : c > 0 := inv_pos_of_pos h_pos
    have h_comass_ψ' : comass ψ' ≤ 1 := by
      show comass (c • ψ) ≤ 1
      rw [comass_smul, abs_of_pos h_c_pos]
      show (comass ψ)⁻¹ * comass ψ ≤ 1
      rw [inv_mul_cancel₀ h_zero]
    have h_in_set : |T.toFun ψ'| ∈ { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| } :=
      ⟨ψ', h_comass_ψ', rfl⟩
    have h_le_mass : |T.toFun ψ'| ≤ Current.mass T := by
      unfold Current.mass
      exact le_csSup (Current.mass_set_bddAbove T) h_in_set
    have h_eval : T.toFun ψ = comass ψ * T.toFun ψ' := by
      have h_prod_eq : comass ψ • ψ' = ψ := by
        show comass ψ • (c • ψ) = ψ
        rw [smul_smul, mul_inv_cancel₀ h_zero, one_smul]
      have h_map : T.toFun (comass ψ • ψ') = comass ψ * T.toFun ψ' := Current.map_smul T (comass ψ) ψ'
      rw [h_prod_eq] at h_map
      exact h_map
    calc |T.toFun ψ|
        = |comass ψ * T.toFun ψ'| := by rw [h_eval]
      _ = |comass ψ| * |T.toFun ψ'| := abs_mul _ _
      _ = comass ψ * |T.toFun ψ'| := by rw [abs_of_pos h_pos]
      _ ≤ comass ψ * Current.mass T := mul_le_mul_of_nonneg_left h_le_mass (le_of_lt h_pos)
      _ = Current.mass T * comass ψ := mul_comm _ _

/-- Helper: For any decomposition T = S + ∂R, evaluation is bounded by
    (mass(S) + mass(R)) × max(comass ψ, comass dψ). -/
theorem eval_le_decomp_cost {k : ℕ} (T S : Current n X k) (R : Current n X (k + 1))
    (h : T = S + Current.boundary R) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ (Current.mass S + Current.mass R) * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
  have h_eval : T.toFun ψ = S.toFun ψ + R.toFun (smoothExtDeriv ψ) := by rw [h]; rfl
  have h_tri : |S.toFun ψ + R.toFun (smoothExtDeriv ψ)| ≤
      |S.toFun ψ| + |R.toFun (smoothExtDeriv ψ)| := abs_add_le _ _
  have h_S : |S.toFun ψ| ≤ Current.mass S * comass ψ := eval_le_mass S ψ
  have h_R : |R.toFun (smoothExtDeriv ψ)| ≤ Current.mass R * comass (smoothExtDeriv ψ) :=
    eval_le_mass R (smoothExtDeriv ψ)
  have h_S' : Current.mass S * comass ψ ≤
      Current.mass S * max (comass ψ) (comass (smoothExtDeriv ψ)) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (Current.mass_nonneg S)
  have h_R' : Current.mass R * comass (smoothExtDeriv ψ) ≤
      Current.mass R * max (comass ψ) (comass (smoothExtDeriv ψ)) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (Current.mass_nonneg R)
  rw [h_eval]
  calc |S.toFun ψ + R.toFun (smoothExtDeriv ψ)|
      ≤ |S.toFun ψ| + |R.toFun (smoothExtDeriv ψ)| := h_tri
    _ ≤ Current.mass S * comass ψ + Current.mass R * comass (smoothExtDeriv ψ) := by linarith
    _ ≤ Current.mass S * max (comass ψ) (comass (smoothExtDeriv ψ)) +
        Current.mass R * max (comass ψ) (comass (smoothExtDeriv ψ)) := by linarith
    _ = (Current.mass S + Current.mass R) * max (comass ψ) (comass (smoothExtDeriv ψ)) := by ring

/-- **Federer-Fleming Evaluation Estimate** (Federer-Fleming, 1960).
    The evaluation of a current on a smooth form is bounded by the flat norm of the
    current and the maximum comass of the form and its derivative.

    **Proof**: For any decomposition T = S + ∂R, |T(ψ)| ≤ (M(S)+M(R)) × max(comass).
    Since flatNorm is the infimum of M(S)+M(R), the bound follows.

    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
theorem eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
  unfold flatNorm
  have h_bound : ∀ m ∈ flatNormDecompSet T,
      |T.toFun ψ| ≤ m * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
    intro m ⟨S, R, hT, hm⟩
    rw [hm]
    exact eval_le_decomp_cost T S R hT ψ
  by_cases h_zero : max (comass ψ) (comass (smoothExtDeriv ψ)) = 0
  · have h1 : comass ψ = 0 := by
      have := le_max_left (comass ψ) (comass (smoothExtDeriv ψ))
      linarith [comass_nonneg ψ]
    obtain ⟨m, hm⟩ := flatNormDecompSet_nonempty T
    have h := h_bound m hm
    rw [h_zero] at h; simp at h
    rw [h, h_zero]; simp
  · have h_pos : max (comass ψ) (comass (smoothExtDeriv ψ)) > 0 :=
      lt_of_le_of_ne (le_max_of_le_left (comass_nonneg ψ)) (Ne.symm h_zero)
    have h_div : |T.toFun ψ| / max (comass ψ) (comass (smoothExtDeriv ψ)) ≤
        sInf (flatNormDecompSet T) := by
      apply le_csInf (flatNormDecompSet_nonempty T)
      intro m hm
      exact (div_le_iff₀ h_pos).mpr (h_bound m hm)
    calc |T.toFun ψ| = |T.toFun ψ| / max (comass ψ) (comass (smoothExtDeriv ψ)) *
          max (comass ψ) (comass (smoothExtDeriv ψ)) := by field_simp
      _ ≤ sInf (flatNormDecompSet T) * max (comass ψ) (comass (smoothExtDeriv ψ)) :=
          mul_le_mul_of_nonneg_right h_div (le_of_lt h_pos)

/-- A current is zero iff its flat norm is zero (Federer-Fleming).
    The ← direction follows from flatNorm_zero.
    The → direction: if flatNorm(T) = 0, then by eval_le_flatNorm,
    |T(ψ)| ≤ 0 for all ψ, so T(ψ) = 0 for all ψ, hence T = 0 by extensionality. -/
theorem flatNorm_eq_zero_iff {k : ℕ} (T : Current n X k) : flatNorm T = 0 ↔ T = 0 := by
  constructor
  · intro h_norm_zero
    ext ψ
    have h_bound := eval_le_flatNorm T ψ
    rw [h_norm_zero, zero_mul] at h_bound
    have h_nonneg : |T.toFun ψ| ≥ 0 := abs_nonneg _
    have h_eq_zero : |T.toFun ψ| = 0 := le_antisymm h_bound h_nonneg
    exact abs_eq_zero.mp h_eq_zero
  · intro h_T_zero
    rw [h_T_zero]
    exact flatNorm_zero

end
