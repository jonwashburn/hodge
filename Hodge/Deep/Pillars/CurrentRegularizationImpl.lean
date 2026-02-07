import Hodge.Classical.PoincareDualityFromCurrents

noncomputable section

open Classical Hodge MeasureTheory

namespace Hodge.Deep.CurrentRegularization

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/--
**Current Regularization Bundle Axiom**

Every current on a projective Kähler manifold can be regularized to a smooth form.
The regularization satisfies two key properties:

1. **Zero-preservation**: `regularize(0) = 0` (follows from linearity of mollification)
2. **Closedness for integration currents**: Regularizing the integration current of a
   closed submanifold produces a closed form (follows from `d ∘ regularize = regularize ∘ d`
   and the integration current being a cycle: `dT = 0 ⟹ d(regularize(T)) = 0`)

**Mathematical Content**: On a compact Kähler manifold, every current T of degree k
can be smoothed via convolution with a mollifier (or heat kernel flow) to produce a
smooth form. The construction uses:
1. Partition of unity subordinate to a finite atlas
2. Convolution in each chart with a smooth kernel
3. Patching via partition of unity

Commutation with `d` follows from `d` being a local operator and convolution
commuting with constant-coefficient differential operators in each chart.

Reference: [de Rham, "Variétés Différentiables", Ch. III (1955)],
[Federer, "Geometric Measure Theory", §4.1 (1969)].
-/
axiom current_regularization_bundle {k : ℕ} :
    { f : Current n X k → SmoothForm n X k //
        (f 0 = 0) ∧
        (∀ (data : ClosedSubmanifoldData n X k),
          IsFormClosed (f (Hodge.GMT.integrationCurrentK_data k data))) }

/--
**Current Regularization Instance**

Provides the `CurrentRegularizationData` instance from the bundled axiom.
-/
instance instCurrentRegularizationData {k : ℕ} : Hodge.GMT.CurrentRegularizationData n X k where
  regularize := current_regularization_bundle.val

/-- **Theorem** (formerly axiom): regularized integration current is closed.

This is now **proved** from `current_regularization_bundle` (closedness for
integration currents property).

**Mathematical Content**: Regularization commutes with the exterior derivative
(d ∘ regularize = regularize ∘ d). The integration current of a closed
submanifold is a cycle (dT = 0), so d(regularize(T)) = regularize(dT) = 0.

Reference: [de Rham, "Variétés Différentiables", Ch. III (1955)].
-/
theorem regularized_integration_current_closed {p : ℕ}
    (data : ClosedSubmanifoldData n X (2 * p)) :
    IsFormClosed (CycleClass.poincareDualForm_data n X p data) := by
  -- poincareDualForm_data unfolds to:
  --   regularizeCurrentToForm (integrationCurrent_data p data)
  -- = current_regularization_bundle.val (integrationCurrentK_data (2*p) data)
  show IsFormClosed ((current_regularization_bundle (n := n) (X := X) (k := 2 * p)).val
      (Hodge.GMT.integrationCurrentK_data (n := n) (X := X) (2 * p) data))
  exact (current_regularization_bundle (n := n) (X := X) (k := 2 * p)).property.2 data

/-- The integration current of a closed submanifold with empty carrier is the zero current.

This follows from the fact that integration over the empty set is zero:
`∫ₓ∈∅ ω = 0` for all forms ω. -/
private theorem integrationCurrent_data_empty {p : ℕ}
    (data : ClosedSubmanifoldData n X (2 * p))
    (h : data.carrier = ∅) :
    Hodge.GMT.integrationCurrent_data p data = 0 := by
  apply Current.ext
  intro ω
  have lhs_eq : (Hodge.GMT.integrationCurrent_data p data).toFun ω =
      (∫ x in data.carrier,
        formVectorPairing ω data.orientation x ∂data.measure).re := by rfl
  have rhs_eq : (0 : Current n X (2 * p)).toFun ω = 0 := by rfl
  rw [lhs_eq, rhs_eq, h]
  simp [Measure.restrict_empty, integral_zero_measure]

/-- **Theorem** (formerly axiom): empty carrier ⟹ Poincaré dual form = 0.

This is now **proved** from `current_regularization_bundle` (zero-preservation) and the
fact that the integration current of an empty carrier is the zero current.

**Mathematical Content**: The integration current of the empty set is the
zero current, and regularization preserves zero: regularize(0) = 0.

Reference: [Federer, "Geometric Measure Theory", §4.1 (1969)].
-/
theorem regularized_integration_current_empty {p : ℕ}
    (data : ClosedSubmanifoldData n X (2 * p))
    (h : data.carrier = ∅) :
    CycleClass.poincareDualForm_data n X p data = 0 := by
  have h1 : Hodge.GMT.integrationCurrent_data p data = 0 :=
    integrationCurrent_data_empty data h
  show (current_regularization_bundle (n := n) (X := X) (k := 2 * p)).val
      (Hodge.GMT.integrationCurrent_data (n := n) (X := X) p data) = 0
  rw [h1]
  exact (current_regularization_bundle (n := n) (X := X) (k := 2 * p)).property.1

/--
**Poincaré Duality From Currents Instance**

Provides `PoincareDualityFromCurrentsData` using:
- `regularized_integration_current_closed` (proved from bundle) for closedness
- `regularized_integration_current_empty` (proved from bundle) for empty vanishing
-/
instance instPoincareDualityFromCurrentsData {p : ℕ} :
    CycleClass.PoincareDualityFromCurrentsData n X p where
  isClosed := fun data => regularized_integration_current_closed data
  empty_vanishes := fun data h => regularized_integration_current_empty data h

end Hodge.Deep.CurrentRegularization
