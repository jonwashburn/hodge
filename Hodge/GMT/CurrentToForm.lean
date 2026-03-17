import Hodge.Analytic.Currents

/-!
# GMT: Current → Smooth Form (interface)

In classical GMT/Hodge theory one often “regularizes” a current to a smooth form.
We expose this as an explicit data interface (no stub implementation).

This file is intentionally **off-proof-track**: it should not be imported by `Hodge`
(the proof-track entry point) until a real construction is provided.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

/-- **Regularization data**: a way to associate a smooth form to a current.

This is a deep analytic construction (mollification / heat flow) and is kept explicit. -/
class CurrentRegularizationData (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] where
  /-- Regularize a current to a smooth form. -/
  regularize : Current n X k → SmoothForm n X k

/-- Regularize a current to a smooth form (explicit data interface). -/
noncomputable def regularizeCurrentToForm {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    [CurrentRegularizationData n X k]
    (T : Current n X k) : SmoothForm n X k :=
  CurrentRegularizationData.regularize (n := n) (X := X) (k := k) T

/-- Companion laws needed to feed the PD-from-currents pipeline honestly.

`CurrentRegularizationData` only records the smoothing map itself; these fields record
the two properties used downstream: cycles regularize to closed forms, and the zero
current regularizes to the zero form. -/
class CurrentRegularizationLaws (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    [CurrentRegularizationData n X k] : Prop where
  regularize_isClosed_of_isCycleAt :
    ∀ T : Current n X k, T.isCycleAt →
      IsFormClosed (regularizeCurrentToForm (n := n) (X := X) (k := k) T)
  regularize_zero :
    regularizeCurrentToForm (n := n) (X := X) (k := k) (0 : Current n X k) = 0

theorem regularizeCurrentToForm_isClosed_of_isCycleAt {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    [CurrentRegularizationData n X k] [CurrentRegularizationLaws n X k]
    (T : Current n X k) (hT : T.isCycleAt) :
    IsFormClosed (regularizeCurrentToForm (n := n) (X := X) (k := k) T) :=
  CurrentRegularizationLaws.regularize_isClosed_of_isCycleAt
    (n := n) (X := X) (k := k) T hT

@[simp] theorem regularizeCurrentToForm_zero {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    [CurrentRegularizationData n X k] [CurrentRegularizationLaws n X k] :
    regularizeCurrentToForm (n := n) (X := X) (k := k) (0 : Current n X k) = 0 :=
  CurrentRegularizationLaws.regularize_zero (n := n) (X := X) (k := k)

end Hodge.GMT
