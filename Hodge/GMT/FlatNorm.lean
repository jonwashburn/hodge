/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.GMT.Mass

/-!
# Flat Norm and Compactness

This file defines the flat norm on currents and states the
Federer-Fleming compactness theorem.

## Main Definitions

* `flatNorm` - F(T) = inf{mass(R) + mass(S) : T = R + ∂S}
* `IntegralCurrent` - Currents with integer coefficients and finite mass

## Main Results

* `flatNorm_le_mass` - F(T) ≤ mass(T)
* `federerFleming` - Compactness in flat norm topology

## References

* Federer-Fleming, "Normal and Integral Currents" (1960)
* Federer, "Geometric Measure Theory", 4.2
* [Washburn-Barghi, Section 7]
-/

noncomputable section

open scoped Manifold
open TopologicalSpace Classical

namespace Hodge.GMT

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

open Hodge.TestForms Hodge.Currents

/-! ## Flat Norm -/

/-- The flat norm of a k-current.
    F(T) = inf{mass(R) + mass(S) : T = R + ∂S} 
    where R is a k-current and S is a (k+1)-current. -/
def flatNorm (T : Current n X k) : ℝ≥0∞ :=
  ⨅ (R : Current n X k) (S : Current n X (k + 1)) 
    (hRS : T = R + Current.boundary S), mass R + mass S

/-- Flat norm is zero iff T is a boundary. -/
theorem flatNorm_eq_zero_iff (T : Current n X k) :
    flatNorm T = 0 ↔ ∃ S : Current n X (k + 1), T = Current.boundary S := sorry

/-- Flat norm is bounded by mass. -/
theorem flatNorm_le_mass (T : Current n X k) : flatNorm T ≤ mass T := by
  -- Take R = T, S = 0 in the infimum
  sorry

/-- Flat norm satisfies the triangle inequality. -/
theorem flatNorm_add (S T : Current n X k) :
    flatNorm (S + T) ≤ flatNorm S + flatNorm T := sorry

/-! ## Flat Norm Topology -/

/-- The flat norm topology on currents. -/
def flatNormTopology : TopologicalSpace (Current n X k) := sorry

/-- Convergence in flat norm. -/
def ConvergesInFlatNorm (seq : ℕ → Current n X k) (T : Current n X k) : Prop :=
  Filter.Tendsto (fun i => flatNorm (seq i - T)) Filter.atTop (nhds 0)

/-! ## Integral Currents -/

/-- An integral current has integer multiplicities and finite mass.
    These are the "geometric" currents that represent cycles. -/
structure IntegralCurrent (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  toCurrent : Current n X k
  hasFiniteMass : HasFiniteMass toCurrent
  hasFiniteBoundaryMass : HasFiniteMass (Current.boundary toCurrent)
  isIntegral : sorry -- Integer multiplicity condition

namespace IntegralCurrent

instance : Coe (IntegralCurrent n X k) (Current n X k) := ⟨IntegralCurrent.toCurrent⟩

/-- Integral currents are closed under addition. -/
instance : Add (IntegralCurrent n X k) := sorry

/-- Boundary of an integral current is integral. -/
def boundary (T : IntegralCurrent n X (k + 1)) : IntegralCurrent n X k := sorry

end IntegralCurrent

/-! ## Federer-Fleming Compactness -/

/-- **Federer-Fleming Compactness Theorem**.
    
    If {T_i} is a sequence of integral currents with uniformly bounded mass
    and boundary mass, then a subsequence converges in flat norm to an
    integral current.
    
    This is one of the deepest results in GMT. We state it as a theorem
    (with proof deferred via sorry) rather than an axiom. -/
theorem federerFleming_compactness
    (seq : ℕ → IntegralCurrent n X k)
    (hMass : ∃ M : ℝ, ∀ i, mass (seq i).toCurrent ≤ M)
    (hBdryMass : ∃ M : ℝ, ∀ i, mass (Current.boundary (seq i).toCurrent) ≤ M) :
    ∃ (subseq : ℕ → ℕ) (T : IntegralCurrent n X k),
      StrictMono subseq ∧ ConvergesInFlatNorm (fun i => (seq (subseq i)).toCurrent) T.toCurrent :=
  sorry

end Hodge.GMT
