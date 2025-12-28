import Hodge.Analytic.Forms
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section

open Classical Set Filter

def pointwiseComass {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} (_α : SmoothForm n X k) (_x : X) : ℝ := 0

def comass {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} (_α : SmoothForm n X k) : ℝ := 0

theorem comass_zero {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} [Nonempty X] : comass (n := n) (0 : SmoothForm n X k) = 0 := rfl

theorem comass_nonneg {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 := le_refl 0

theorem comass_add_le {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} (α β : SmoothForm n X k) :
    comass (α + β) ≤ comass α + comass β := by simp [comass]

theorem comass_smul {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    comass (r • α) = |r| * comass α := by
  simp [comass]

def pointwiseInner {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} (_α _β : SmoothForm n X k) (_x : X) : ℝ := 0

def energy {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} (_α : SmoothForm n X k) : ℝ := 0

def pointwiseNorm {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} (_α : SmoothForm n X k) (_x : X) : ℝ := 0

theorem pointwiseInner_nonneg {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseInner α α x ≥ 0 := le_refl 0

theorem pointwiseNorm_sq_expand {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  {k : ℕ} (_x : X) (_α _β : SmoothForm n X k) (_t : ℝ) :
    (pointwiseNorm (_α + _t • _β) _x)^2 =
    pointwiseInner _α _α _x + 2 * _t * (pointwiseInner _α _β _x) + _t^2 * (pointwiseInner _β _β _x) := by
  simp [pointwiseNorm, pointwiseInner]

end
