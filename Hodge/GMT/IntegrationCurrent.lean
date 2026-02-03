import Hodge.GMT.Current
import Hodge.Analytic.Currents
import Hodge.Analytic.Integration.HausdorffMeasure

/-!
# GMT: Integration Currents

This module provides the **integration current** infrastructure connecting the GMT layer
to the real integration machinery in `Hodge.Analytic.Currents`.

## Round 10 Update (M4: Currents Bridge)

The integration current is now **properly wired** to the `Hodge.Analytic.Currents`
infrastructure:

-- `integrationCurrentReal` uses `ClosedSubmanifoldStokesData.toIntegrationData`,
  which connects a concrete `ClosedSubmanifoldData` to `IntegrationData → Current`.
-- The underlying integration uses Hausdorff integration on oriented rectifiable data.
- Linearity, boundedness, and Stokes bounds are proven (not axiomatized)

## Mathematical Content

For a closed (compact, boundaryless) submanifold Z ⊂ X of complex dimension p:

  `[Z](ω) = ∫_Z ω`

where the integral is with respect to the 2p-dimensional Hausdorff measure.

## Key Definitions

- `integrationCurrentReal`: The real integration current using `IntegrationData.closedSubmanifold`
- `integrationCurrent`: Lightweight alias for the proof track

## Connection to Cohomology

The integration current `[Z]` induces a cohomology class via:
1. `[Z]` acts on closed forms by integration
2. This action descends to cohomology (by Stokes: `[Z](dω) = ∫_∂Z ω = 0` for closed Z)
3. The cohomology class is the Poincaré dual of Z

See `Hodge.GMT.PoincareDuality` for the full construction.

## References

- [H. Federer, "Geometric Measure Theory", 1969, §4.1.7]
- [Griffiths-Harris, "Principles of Algebraic Geometry", 1978, Ch. 0]
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

namespace Hodge.GMT

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-! ## Integration Current (Real Implementation)

The following definitions wire to the actual integration infrastructure in
`Hodge.Analytic.Currents`, which uses `ClosedSubmanifoldData` /
`OrientedRectifiableSetData` and `hausdorffIntegrate`. -/

/-- **Real Integration Current** (from closed submanifold data).

    For a set Z with Stokes data (closed submanifold), this produces a `Current`
    that genuinely integrates forms over Z using the Hausdorff measure infrastructure.

    **Mathematical Definition**:
    `[Z](ω) = ∫_Z ω` where the integral is via `hausdorffIntegrate`.

    Reference: [Federer, "Geometric Measure Theory", 1969, §4.1.7]. -/
noncomputable def integrationCurrentReal (k : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X k Z] : DeRhamCurrent n X k :=
  (ClosedSubmanifoldStokesData.toIntegrationData (n := n) (X := X) (k := k) (Z := Z)).toCurrent

/-- Integration current in degree `k` over a set `Z` (requires Stokes data). -/
noncomputable def integrationCurrentK (k : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X k Z] : DeRhamCurrent n X k :=
  integrationCurrentReal (n := n) (X := X) k Z

/-- Integration current with Stokes data (the preferred interface).

    This is the main entry point for constructing integration currents over closed
    submanifolds. The `ClosedSubmanifoldStokesData` instance provides the Stokes property. -/
noncomputable def integrationCurrentWithStokes (k : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X k Z] : DeRhamCurrent n X k :=
  integrationCurrentReal (n := n) (X := X) k Z

/-- Integration current for a codimension parameter `p`, returning degree `2*p`.

    **Note**: Complex submanifolds of complex dimension p have real dimension 2p,
    so the integration current lives in degree 2p (as a k-current for k = 2p forms).

This matches the signature used in `docs/OPERATIONAL_PLAN_5_AGENTS.md`. -/
noncomputable def integrationCurrent (p : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X (2 * p) Z] : DeRhamCurrent n X (2 * p) :=
  integrationCurrentK (n := n) (X := X) (k := 2 * p) Z

/-- Linearity of the integration current evaluation (degree-`k` form). -/
theorem integrationCurrentK_linear (k : ℕ) (Z : Set X) (c : ℝ)
    [ClosedSubmanifoldStokesData n X k Z]
    (ω₁ ω₂ : SmoothForm n X k) :
    (integrationCurrentK (n := n) (X := X) k Z).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrentK (n := n) (X := X) k Z).toFun ω₁ +
        (integrationCurrentK (n := n) (X := X) k Z).toFun ω₂ :=
by
  simpa [DeRhamCurrent] using
    (Hodge.GMT.current_eval_linear (T := integrationCurrentK (n := n) (X := X) k Z) c ω₁ ω₂)

/-- Linearity of the integration current evaluation (codimension form, degree `2*p`). -/
theorem integrationCurrent_linear (p : ℕ) (Z : Set X) (c : ℝ)
    [ClosedSubmanifoldStokesData n X (2 * p) Z]
    (ω₁ ω₂ : SmoothForm n X (2 * p)) :
    (integrationCurrent (n := n) (X := X) p Z).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrent (n := n) (X := X) p Z).toFun ω₁ +
        (integrationCurrent (n := n) (X := X) p Z).toFun ω₂ :=
by
  simpa [DeRhamCurrent] using
    (Hodge.GMT.current_eval_linear (T := integrationCurrent (n := n) (X := X) p Z) c ω₁ ω₂)

/-! ## Integration Current Properties (with Stokes data) -/

/-- The real integration current uses `ClosedSubmanifoldStokesData.toIntegrationData`. -/
theorem integrationCurrentReal_toFun_eq (k : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X k Z] (ω : SmoothForm n X k) :
    (integrationCurrentReal (n := n) (X := X) k Z).toFun ω =
      (ClosedSubmanifoldStokesData.toIntegrationData (n := n) (X := X) (k := k) (Z := Z)).integrate ω := by
  rfl

/-! ## Connection to Cohomology

The integration current defines a linear functional on forms that descends to cohomology.
This is the foundation for the cycle class map `Z ↦ [Z]`. -/

/-- **Integration induces cohomology pairing** (conceptual statement).

    For a closed submanifold Z and a closed form ω:
    - `[Z](ω)` depends only on the cohomology class of ω
    - This defines a map `H^k(X) → ℝ`, which by Poincaré duality corresponds to
      an element of `H^{2n-k}(X)`

    **Mathematical Content** (Stokes theorem):
    If ω = dη, then `[Z](ω) = [Z](dη) = ∫_Z dη = ∫_∂Z η = 0` (since ∂Z = ∅).
    Therefore `[Z]` descends to a well-defined functional on cohomology. -/
theorem integration_descends_to_cohomology (k : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X (k + 1) Z]
    (η : SmoothForm n X k) :
    (integrationCurrentReal (n := n) (X := X) (k + 1) Z).toFun (smoothExtDeriv η) = 0 := by
  -- Use the Stokes bound from the closed-submanifold integration data.
  let data :=
    ClosedSubmanifoldStokesData.toIntegrationData (n := n) (X := X) (k := k + 1) (Z := Z)
  have h := data.stokes_bound (k' := k) rfl η
  -- Since bdryMass = 0 for closed submanifolds, the bound forces the integral to be 0.
  have hbdry : data.bdryMass = 0 := by
    simp [data, ClosedSubmanifoldStokesData.toIntegrationData, ClosedSubmanifoldData.toIntegrationData]
  have h0 :
      |data.integrate (smoothExtDeriv η)| ≤ 0 := by
    simpa [hbdry, MulZeroClass.zero_mul] using h
  exact abs_nonpos_iff.mp h0

end Hodge.GMT
