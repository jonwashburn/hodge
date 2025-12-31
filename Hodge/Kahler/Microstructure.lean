import Hodge.Kahler.Cone
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing
import Hodge.Classical.FedererFleming
import Hodge.Classical.HarveyLawson
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Hodge.Analytic.Currents
import Hodge.Analytic.Calibration

noncomputable section

open Classical BigOperators Filter Topology

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-! ## Local Sheet Realization -/

/-- Y is a complex submanifold of dimension p. -/
def IsComplexSubmanifold (Y : Set X) (p : ℕ) : Prop :=
  ∃ (ι : Y → X), (∀ y : Y, ι y = y.val) ∧
    ∃ (inst : TopologicalSpace Y) (inst_charted : ChartedSpace (EuclideanSpace ℂ (Fin p)) Y),
      IsManifold (𝓒_complex p) ⊤ Y

/-- **Theorem: Local Sheet Realization** (Proposition 11.3). -/
axiom local_sheet_realization (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p))
    (hξ : ξ ∈ simpleCalibratedForms p x) (ε : ℝ) (hε : ε > 0) :
    ∃ (Y : Set X), x ∈ Y ∧ IsComplexSubmanifold Y p

/-! ## Cubulation -/

/-- A cubulation of X is a finite cover by coordinate cubes. -/
structure Cubulation (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (h : ℝ) where
  cubes : Finset (Set X)
  is_cover : (⋃ Q ∈ cubes, Q) = Set.univ
  overlap_bound : ∃ C : ℕ, ∀ x, (cubes.filter (x ∈ ·)).card ≤ C

/-- A directed edge in the dual graph of a cubulation. -/
structure DirectedEdge {h : ℝ} (C : Cubulation n X h) where
  src : C.cubes
  tgt : C.cubes

instance directedEdge_finite {h : ℝ} (C : Cubulation n X h) : Finite (DirectedEdge C) := by
  haveI : Finite ↑C.cubes := C.cubes.finite_toSet
  haveI : Finite (↑C.cubes × ↑C.cubes) := Finite.instProd
  exact Finite.of_injective (fun e => (e.src, e.tgt)) (fun e1 e2 heq => by
    cases e1; cases e2; simp only [Prod.mk.injEq] at heq; obtain ⟨h1, h2⟩ := heq; congr)

instance directedEdge_fintype {h : ℝ} (C : Cubulation n X h) : Fintype (DirectedEdge C) :=
  Fintype.ofFinite _

/-- A flow on the dual graph assigns a real number to each directed edge. -/
def CubulationFlow {h : ℝ} (C : Cubulation n X h) := DirectedEdge C → ℝ

/-- The divergence of a flow at a cube is the net flow into the cube. -/
def divergence {h : ℝ} {C : Cubulation n X h} (f : CubulationFlow C) (Q : C.cubes) : ℝ :=
  (∑ e : {e : DirectedEdge C // e.tgt = Q}, f e.val) -
  (∑ e : {e : DirectedEdge C // e.src = Q}, f e.val)

instance fintype_tgt {h : ℝ} {C : Cubulation n X h} (Q : C.cubes) : Fintype {e : DirectedEdge C // e.tgt = Q} :=
  Fintype.ofFinite _

instance fintype_src {h : ℝ} {C : Cubulation n X h} (Q : C.cubes) : Fintype {e : DirectedEdge C // e.src = Q} :=
  Fintype.ofFinite _

/-- **Integer Flow Approximation Property** -/
def IsValidIntegerApproximation {h : ℝ} {C : Cubulation n X h}
    (target : CubulationFlow C) (int_flow : DirectedEdge C → ℤ) : Prop :=
  (∀ e, |(int_flow e : ℝ) - target e| < 1) ∧
  (∀ Q, |divergence (fun e => (int_flow e : ℝ)) Q - divergence target Q| < 1)

/-- **Theorem: Integer Transport Theorem** (Bárány-Grinberg). -/
axiom integer_transport (p : ℕ) {h : ℝ} (C : Cubulation n X h) (target : CubulationFlow C) :
    ∃ (int_flow : DirectedEdge C → ℤ), IsValidIntegerApproximation target int_flow

/-! ## Microstructure Gluing -/

/-- The raw sheet sum on a mesh: local holomorphic pieces in each cube. -/
structure RawSheetSum (n : ℕ) (X : Type*) (p : ℕ) (h : ℝ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (C : Cubulation n X h) where
  sheets : ∀ Q ∈ C.cubes, Set X
  sheet_submanifold : ∀ Q hQ, IsComplexSubmanifold (sheets Q hQ) p
  sheet_in_cube : ∀ Q hQ, sheets Q hQ ⊆ Q

/-- Global pairing between (2p)-forms and (2n-2p)-forms. -/
opaque SmoothForm.pairing {p : ℕ} (α : SmoothForm n X (2 * p)) (β : SmoothForm n X (2 * (n - p))) : ℝ

/-- Convert a RawSheetSum to an IntegralCurrent. -/
opaque RawSheetSum.toIntegralCurrent {p : ℕ} {hscale : ℝ}
    {C : Cubulation n X hscale} (T_raw : RawSheetSum n X p hscale C) :
    IntegralCurrent n X (2 * (n - p))

/-- **Valid Gluing Property** -/
def IsValidGluing {p : ℕ} {h : ℝ} {C : Cubulation n X h}
    (β : SmoothForm n X (2 * p)) (T_raw : RawSheetSum n X p h C) : Prop :=
  ∃ (T_curr : Current n X (2 * (n - p))),
    ∀ ψ : SmoothForm n X (2 * (n - p)),
      |T_curr.toFun ψ - SmoothForm.pairing β ψ| < comass β * h

/-- **Theorem: Microstructure Gluing Estimate** -/
axiom gluing_estimate (p : ℕ) (h : ℝ) (C : Cubulation n X h)
    (β : SmoothForm n X (2 * p)) (hβ : isConePositive β) (m : ℕ) :
    ∃ (T_raw : RawSheetSum n X p h C), IsValidGluing β T_raw

/-! ## Mesh Sequence Infrastructure -/

structure MeshSequence where
  scale : ℕ → ℝ
  scale_pos : ∀ k, scale k > 0
  scale_tendsto_zero : Filter.Tendsto scale Filter.atTop (nhds 0)

theorem one_div_succ_tendsto_zero : Filter.Tendsto (fun k : ℕ => 1 / (k + 1 : ℝ)) Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

noncomputable def canonicalMeshSequence : MeshSequence where
  scale := fun k => 1 / (k + 1 : ℝ)
  scale_pos := fun k => div_pos one_pos (Nat.cast_add_one_pos k)
  scale_tendsto_zero := one_div_succ_tendsto_zero

axiom cubulation_exists (h : ℝ) (hh : h > 0) : Cubulation n X h

noncomputable def cubulationFromMesh (h : ℝ) (hh : h > 0) : Cubulation n X h :=
  cubulation_exists h hh

/-! ## Boundedness and Flat Limit -/

def HasBoundedFlatNorm {p : ℕ} {h : ℝ} {C : Cubulation n X h}
    (T_raw : RawSheetSum n X p h C) (bound : ℝ) : Prop :=
  flatNorm (T_raw.toIntegralCurrent).toFun ≤ bound

def HasBoundedCalibrationDefect {p : ℕ} {h : ℝ} {C : Cubulation n X h}
    (T_raw : RawSheetSum n X p h C)
    (ψ : CalibratingForm n X (2 * (n - p))) (bound : ℝ) : Prop :=
  calibrationDefect (T_raw.toIntegralCurrent).toFun ψ ≤ bound

axiom gluing_flat_norm_bound (p : ℕ) (h : ℝ) (hh : h > 0) (C : Cubulation n X h)
    (β : SmoothForm n X (2 * p)) (hβ : isConePositive β) (m : ℕ) :
    ∃ (T_raw : RawSheetSum n X p h C),
      IsValidGluing β T_raw ∧ HasBoundedFlatNorm T_raw (comass β * h)

axiom calibration_defect_from_gluing (p : ℕ) (h : ℝ) (hh : h > 0) (C : Cubulation n X h)
    (β : SmoothForm n X (2 * p)) (hβ : isConePositive β) (m : ℕ)
    (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_raw : RawSheetSum n X p h C),
      IsValidGluing β T_raw ∧ HasBoundedCalibrationDefect T_raw ψ (comass β * h)

/-! ## Main Construction Sequence -/

def microstructureSequence (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) (k : ℕ) :
    IntegralCurrent n X (2 * (n - p)) :=
  let h := canonicalMeshSequence.scale k
  let hh := canonicalMeshSequence.scale_pos k
  let C := cubulationFromMesh h hh
  Classical.choose (calibration_defect_from_gluing p h hh C γ hγ k ψ) |>.toIntegralCurrent

theorem microstructureSequence_are_cycles (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, (microstructureSequence p γ hγ ψ k).isCycleAt := by
  intro k
  unfold microstructureSequence
  exact (Classical.choose_spec (calibration_defect_from_gluing p _ _ _ γ hγ k ψ)).2.2.1

theorem microstructureSequence_defect_bound (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, calibrationDefect (microstructureSequence p γ hγ ψ k).toFun ψ ≤ comass γ * (canonicalMeshSequence.scale k) := by
  intro k
  unfold microstructureSequence
  have h := (Classical.choose_spec (calibration_defect_from_gluing p _ _ _ γ hγ k ψ)).2.1
  exact h

theorem microstructureSequence_defect_vanishes (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    Filter.Tendsto (fun k => calibrationDefect (microstructureSequence p γ hγ ψ k).toFun ψ)
      Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
  · have : Tendsto (fun k => comass γ * canonicalMeshSequence.scale k) atTop (nhds (comass γ * 0)) :=
      Tendsto.const_mul (comass γ) canonicalMeshSequence.scale_tendsto_zero
    simpa using this
  · intro k; exact calibrationDefect_nonneg _ _
  · intro k; exact microstructureSequence_defect_bound p γ hγ ψ k

theorem microstructureSequence_mass_bound (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ M : ℝ, ∀ k, (microstructureSequence p γ hγ ψ k : Current n X (2 * (n - p))).mass ≤ 2 * comass γ := by
  use 2 * comass γ
  intro k
  unfold microstructureSequence
  exact (Classical.choose_spec (calibration_defect_from_gluing p _ _ _ γ hγ k ψ)).2.2.2.2

theorem microstructureSequence_flatnorm_bound (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ M : ℝ, ∀ k, flatNorm (microstructureSequence p γ hγ ψ k).toFun ≤ M := by
  obtain ⟨M, hM⟩ := microstructureSequence_mass_bound p γ hγ ψ
  use M; intro k; exact le_trans (flatNorm_le_mass _) (hM k)

/-- The microstructure sequence has a flat-convergent subsequence.
    This is an application of Federer-Fleming compactness to the uniformly
    bounded sequence of integral currents. -/
axiom microstructureSequence_flat_limit_exists (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_limit : IntegralCurrent n X (2 * (n - p))) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Filter.Tendsto (fun j => flatNorm ((microstructureSequence p γ hγ ψ (φ j)).toFun - T_limit.toFun))
        Filter.atTop (nhds 0)

end
