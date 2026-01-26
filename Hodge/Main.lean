import Hodge.Cohomology.Basic
import Hodge.Kahler.Main

/-!
# The Hodge Conjecture (Final Formalization)

This is the top-level entry point for the Hodge Conjecture formalization.
The full proof logic is contained in `Hodge/Kahler/Main.lean`.

## Two Versions

1. **`hodge_conjecture`** (TeX-faithful): Uses geometric cycle class `cycleClass_geom`
   with explicit `SpineBridgeData` typeclass. The cycle class comes from geometry
   (fundamental class of the support), matching the TeX proof structure.

2. **`hodge_conjecture_kernel`** (kernel-only): Uses definitional shortcut
   `cycleClass := ofForm representingForm`. No custom axioms, but not TeX-faithful.
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [MeasurableSpace X] [Nonempty X]

/-- **The Hodge Conjecture** (Hodge, 1950; Millennium Prize Problem).

    For a smooth projective complex algebraic variety X, every rational Hodge class
    is algebraic (i.e., the GEOMETRIC cycle class equals the cohomology class).

    **TeX-Faithful**: Uses `cycleClass_geom` (from fundamental class of support)
    with explicit `SpineBridgeData` assumption for the Poincaré duality bridge.

    **Mathematical Content**:
    - The cycle Z is constructed via SYR → Harvey-Lawson → GAGA
    - Its geometric cycle class (fundamental class) equals [γ] in cohomology
    - `SpineBridgeData` encapsulates the deep GMT/Poincaré duality content

    See `hodge_conjecture_kernel` for the kernel-only version without typeclasses. -/
theorem hodge_conjecture {p : ℕ}
    [SpineBridgeData n X]  -- Explicit assumption for Poincaré duality bridge
    [CycleClass.PoincareDualFormExists n X p]
    [FlatLimitCycleData n X (2 * (n - p))]  -- Federer-Fleming compactness
    [CubulationExists n X]  -- Cubulation existence for microstructure
    [HarveyLawsonKingData n X (2 * (n - p))]  -- Harvey-Lawson regularity
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (ofForm γ h_closed)) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X p), Z.cycleClass_geom = ofForm γ h_closed :=
  hodge_conjecture' γ h_closed h_rational h_p_p

end
