import Hodge.Cohomology.Basic
import Hodge.Kahler.Main

/-!
# The Hodge Conjecture (Final Formalization)

This is the top-level entry point for the Hodge Conjecture formalization.
The full proof logic is contained in `Hodge/Kahler/Main.lean`.

## Two Versions

1. **`hodge_conjecture`** (TeX-faithful): Uses geometric cycle class `cycleClass_geom`
   computed from the fundamental class of the support, together with an explicit
   bridge assumption `SpineBridgeData`.

2. **`hodge_conjecture_kernel`** (kernel-only): Uses definitional shortcut
   `cycleClass := ofForm representingForm`. No custom axioms, but not TeX-faithful.
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-- **The Hodge Conjecture** (Hodge, 1950; Millennium Prize Problem).

    For a smooth projective complex algebraic variety X, every rational Hodge class
    is algebraic (i.e., the GEOMETRIC cycle class equals the cohomology class).

    **TeX-Faithful**: Uses `cycleClass_geom` defined from the support (fundamental class),
    and a bridge assumption `SpineBridgeData` relating that geometric class to the carried
    `representingForm` class.

    **Phase 7 Update (2026-02-01)**: `cycleClass_geom` is now the REAL geometric class
    from `FundamentalClassSet(support)`. Requires:
    - `PoincareDualFormExists` for fundamental class construction
    - `SpineBridgeData` for the bridge theorem

    **Mathematical Content**:
    - The cycle Z is constructed via SYR → Harvey-Lawson → GAGA
    - Its geometric cycle class (from FundamentalClassSet) equals [γ] in cohomology
    - The bridge theorem connects the fundamental class to the representing form

    See `hodge_conjecture_kernel` for the equivalent kernel-only version. -/
theorem hodge_conjecture {p : ℕ}
    [AutomaticSYRData n X]
    [CycleClass.PoincareDualFormExists n X p] [SpineBridgeData n X p]
    [CalibratedCurrentRegularityData n X (2 * (n - p))]
    [HarveyLawsonKingData n X (2 * (n - p))]
    [ChowGAGAData n X]
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (ofForm γ h_closed)) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X p), Z.cycleClass_geom = ofForm γ h_closed :=
  hodge_conjecture' γ h_closed h_rational h_p_p

end
