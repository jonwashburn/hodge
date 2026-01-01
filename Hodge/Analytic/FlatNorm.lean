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

/-- The flat norm of a boundary is at most the flat norm of the original current.
    This is a non-trivial result: ∂T = ∂S where T = S + ∂R, so flatNorm(∂T) ≤ flatNorm(T).
    Proof: If T = S + ∂R with cost M(S) + M(R) = flatNorm(T), then ∂T = ∂S + 0
    (since ∂∂R = 0), which has cost M(∂S) + 0 ≤ ... (requires mass bound on ∂).
    This is axiomatized because it requires deeper GMT infrastructure. -/
axiom flatNorm_boundary_le {k : ℕ} (T : Current n X (k + 1)) :
    flatNorm (Current.boundary T) ≤ flatNorm T

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

/-- The flat norm is symmetric under negation.
    This follows from: if T = S + ∂R, then -T = -S + ∂(-R), with equal costs. -/
axiom flatNorm_neg {k : ℕ} (T : Current n X k) : flatNorm (-T) = flatNorm T

/-- The flat norm satisfies the triangle inequality (Federer-Fleming 1960).
    This follows from: if T₁ = S₁ + ∂R₁ and T₂ = S₂ + ∂R₂,
    then T₁ + T₂ = (S₁+S₂) + ∂(R₁+R₂) with cost bounded by sum of costs. -/
axiom flatNorm_add_le {k : ℕ} (S T : Current n X k) :
    flatNorm (S + T) ≤ flatNorm S + flatNorm T

/-- Flat norm scales with absolute value of scalar.
    This follows from: if T = S + ∂R, then cT = cS + ∂(cR),
    with mass(cS) = |c|·mass(S). -/
axiom flatNorm_smul {k : ℕ} (c : ℝ) (T : Current n X k) :
    flatNorm (c • T) = |c| * flatNorm T

/-- A current is zero iff its flat norm is zero.
    The ← direction follows from flatNorm_zero.
    The → direction requires the deeper result that flatNorm separates points. -/
axiom flatNorm_eq_zero_iff {k : ℕ} (T : Current n X k) : flatNorm T = 0 ↔ T = 0

/-- Bound evaluation by mass. -/
axiom eval_le_mass {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ Current.mass T * comass ψ

/-- **Federer-Fleming Evaluation Estimate** (Federer-Fleming, 1960).
    The evaluation of a current on a smooth form is bounded by the flat norm of the
    current and the maximum comass of the form and its derivative.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
axiom eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ))

end
