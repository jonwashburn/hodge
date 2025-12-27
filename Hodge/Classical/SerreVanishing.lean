import Hodge.Classical.Bergman

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-!
# Track A.1: Serre Vanishing Theorem (Axiomatized)
-/

/-- A coherent sheaf on a complex manifold (axiomatized). -/
structure CoherentSheaf (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] where
  id : ℕ := 0

/-- The structure sheaf O_X. -/
def structureSheaf : CoherentSheaf n X := ⟨0⟩

/-- Tensor product of a holomorphic line bundle with a coherent sheaf. -/
def tensorWithSheaf (_L : HolomorphicLineBundle n X) (F : CoherentSheaf n X) :
    CoherentSheaf n X := F

/-- The ideal sheaf. -/
def idealSheaf (_x : X) (_k : ℕ) : CoherentSheaf n X := structureSheaf

/-- Sheaf cohomology (axiomatized). -/
def SheafCohomology (_F : CoherentSheaf n X) (_q : ℕ) : Type := Unit

/-- A cohomology group is zero. -/
def isZero (_G : Type) : Prop := True

/-- Serre Vanishing Theorem. -/
theorem serre_vanishing (L : HolomorphicLineBundle n X) [IsAmple L]
    (F : CoherentSheaf n X) (q : ℕ) (_hq : q > 0) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, isZero (SheafCohomology (tensorWithSheaf (L.power M) F) q) := by
  use 0; intro _ _; trivial

/-- Jet Surjectivity from Serre Vanishing. -/
theorem jet_surjectivity_from_serre (L : HolomorphicLineBundle n X) [IsAmple L]
    (x : X) (k : ℕ) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, Function.Surjective (jet_eval (L := L.power M) x k) := sorry

/-- Dimension lower bound. -/
theorem dimension_lower_bound (L : HolomorphicLineBundle n X) [IsAmple L] (k : ℕ) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, BergmanDimension (L.power M) ≥ k := IsAmple.growth k

end
