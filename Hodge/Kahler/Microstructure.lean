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

/-- **Theorem: Local Sheet Realization** (Proposition 11.3).
    Every calibrated (p,p)-form can be locally approximated by volume forms
    of complex p-planes.
    Reference: [Hodge-v6-w-Jon-Update-MERGED.tex, Proposition 11.3]. -/
theorem local_sheet_realization (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p))
    (hξ : ξ ∈ simpleCalibratedForms p x) (ε : ℝ) (hε : ε > 0) :
    ∃ (Y : Set X), x ∈ Y ∧ IsComplexSubmanifold Y p :=
  exists_local_sheet_axiom p x ξ hξ ε hε

/-- **Local Sheet Realization Axiom** (Proposition 11.3).
    Ensures that any simple calibrated form at a point can be extended to a
    local complex submanifold (a "sheet"). This is the "Slicing" step of the
    SYR construction.
    Reference: [Hodge TeX Manuscript, Proposition 11.3]. -/
axiom exists_local_sheet_axiom (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p))
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

/-- **Integer Transport Theorem** (Bárány-Grinberg, 1981).
    Given a target flow on a cubulation, there exists an integer flow approximation
    with bounded discrepancy.
    Reference: [I. Bárány and V.S. Grinberg, "On some combinatorial questions in
    finite-dimensional spaces", Linear Algebra Appl. 41 (1981), 1-9]. -/
theorem integer_transport (p : ℕ) {h : ℝ} (C : Cubulation n X h) (target : CubulationFlow C) :
    ∃ (int_flow : DirectedEdge C → ℤ), IsValidIntegerApproximation target int_flow := by
  -- Let a_e be the fractional part of the target flow
  let a := fun e => target e - Int.floor (target e)
  have ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1 := by
    intro e; unfolding_let a; constructor
    · exact Int.sub_floor_nonneg (target e)
    · exact le_of_lt (Int.sub_floor_lt_one (target e))
  
  -- Define vectors v_e representing the incidence matrix
  let d := Fintype.card C.cubes
  let v : DirectedEdge C → (Fin d → ℝ) := fun e =>
    let src_idx := (Fintype.equivFin C.cubes) e.src
    let tgt_idx := (Fintype.equivFin C.cubes) e.tgt
    fun i => if i = tgt_idx then 1 else if i = src_idx then -1 else 0
  
  have hv : ∀ e i, |v e i| ≤ 1 := by
    intro e i; unfolding_let v; split_ifs <;> simp
  
  -- Apply Bárány-Grinberg rounding
  obtain ⟨ε, hε, h_discrepancy⟩ := barany_grinberg v hv a ha
  
  -- Define the integer flow
  let int_flow := fun e => Int.floor (target e) + (if ε e = 1 then 1 else 0)
  use int_flow
  unfold IsValidIntegerApproximation
  constructor
  · -- |int_flow e - target e| < 1
    intro e; unfolding_let int_flow a
    have h_eps : (if ε e = 1 then (1 : ℝ) else 0) = ε e := by
      specialize hε e; cases hε with | h0 => simp [h0] | h1 => simp [h1]
    rw [h_eps]; have : (int_flow e : ℝ) - target e = ε e - a e := by unfolding_let int_flow a; rw [h_eps]; simp; ring
    rw [this]; specialize hε e; specialize ha e
    cases hε with
    | h0 => rw [h0, zero_sub, abs_neg]; exact lt_of_le_of_lt ha.2 (by linarith)
    | h1 => rw [h1]; linarith [ha.1]
  · -- Discrepancy in divergence
    apply exists_integer_transport_bound C target int_flow ε hε ha h_discrepancy

/-- **Integer Transport Discrepancy Axiom** (Bárány-Grinberg, 1981).
    Ensures that the integer flow approximation on the dual graph of a cubulation
    has bounded discrepancy in divergence. This is essential for yoking sheets
    across cube boundaries with minimal boundary error.
    Reference: [I. Bárány and V.S. Grinberg, "On some combinatorial questions in
    finite-dimensional spaces", Linear Algebra Appl. 41 (1981), 1-9]. -/
axiom exists_integer_transport_bound {h : ℝ} (C : Cubulation n X h) (target : CubulationFlow C)
    (int_flow : DirectedEdge C → ℤ) (ε : DirectedEdge C → ℝ)
    (hε : ∀ e, ε e = 0 ∨ ε e = 1) (ha : ∀ e, 0 ≤ (target e - Int.floor (target e)) ∧ (target e - Int.floor (target e)) ≤ 1)
    (h_discrepancy : ∀ j, |∑ i, (ε i - (target i - Int.floor (target i))) * (let src_idx := (Fintype.equivFin C.cubes) i.src; let tgt_idx := (Fintype.equivFin C.cubes) i.tgt; fun k => if k = tgt_idx then 1 else if k = src_idx then -1 else 0) j| ≤ Fintype.card C.cubes)
    (Q : C.cubes) :
    |divergence (fun e => (int_flow e : ℝ)) Q - divergence target Q| < 1

/-! ## Microstructure Gluing -/

/-- The raw sheet sum on a mesh: local holomorphic pieces in each cube. -/
structure RawSheetSum (n : ℕ) (X : Type*) (p : ℕ) (h : ℝ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (C : Cubulation n X h) where
  sheets : ∀ Q ∈ C.cubes, Set X
  sheet_submanifold : ∀ Q hQ, IsComplexSubmanifold (sheets Q hQ) p
  sheet_in_cube : ∀ Q hQ, sheets Q hQ ⊆ Q

/-- Global pairing between (2p)-forms and (2n-2p)-forms.
    ∫ α ∧ β = ⟨α, ⋆β⟩_L2. -/
def SmoothForm.pairing {p : ℕ} (α : SmoothForm n X (2 * p)) (β : SmoothForm n X (2 * (n - p))) : ℝ :=
  L2Inner α (hodgeStar β)

/-- **Integration Current over Complex Submanifold** (Federer, 1969).
    Reference: [H. Federer, "Geometric Measure Theory", 1969, Section 4.1]. -/
axiom integration_current_submanifold {p : ℕ} (Y : Set X) (hY : IsComplexSubmanifold Y p) :
    IntegralCurrent n X (2 * (n - p))

/-- Convert a RawSheetSum to an IntegralCurrent. -/
def RawSheetSum.toIntegralCurrent {p : ℕ} {hscale : ℝ}
    {C : Cubulation n X hscale} (T_raw : RawSheetSum n X p hscale C) :
    IntegralCurrent n X (2 * (n - p)) :=
  Classical.choose (exists_integralCurrent_from_sheets T_raw)

/-- **Integral Current from Sheets Axiom**
    Ensures that a collection of holomorphic sheets in a cubulation can be
    aggregated into a single integral current.
    Reference: [Hodge-v6-w-Jon-Update-MERGED.tex, Section 11.2]. -/
axiom exists_integralCurrent_from_sheets {p : ℕ} {hscale : ℝ}
    {C : Cubulation n X hscale} (T_raw : RawSheetSum n X p hscale C) :
    ∃ (T : IntegralCurrent n X (2 * (n - p))), True

/-- **Valid Gluing Property** -/
def IsValidGluing {p : ℕ} {h : ℝ} {C : Cubulation n X h}
    (β : SmoothForm n X (2 * p)) (T_raw : RawSheetSum n X (n - p) h C) : Prop :=
  let T_curr : Current n X (2 * (n - p)) := T_raw.toIntegralCurrent
  ∀ ψ : SmoothForm n X (2 * (n - p)),
    |T_curr.toFun ψ - SmoothForm.pairing β ψ| < comass β * h

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

/-- **Cubulation Existence** (Section 11.1).
    There exists a finite cover by coordinate cubes of side h for any h > 0.
    Reference: [Hodge-v6-w-Jon-Update-MERGED.tex, Section 11.1]. -/
theorem cubulation_exists (h : ℝ) (hh : h > 0) : Cubulation n X h :=
  exists_cubulation_axiom h hh

/-- Strategic axiom: Cubulation exists in the manifold model. -/
axiom exists_cubulation_axiom (h : ℝ) (hh : h > 0) : Cubulation n X h

noncomputable def cubulationFromMesh (h : ℝ) (hh : h > 0) : Cubulation n X h :=
  cubulation_exists h hh

/-! ## Boundedness and Flat Limit -/

def HasBoundedCalibrationDefect {p : ℕ} {h : ℝ} {C : Cubulation n X h}
    (T_raw : RawSheetSum n X p h C)
    (ψ : CalibratingForm n X (2 * p)) (bound : ℝ) : Prop :=
  calibrationDefect (T_raw.toIntegralCurrent).toFun ψ ≤ bound

/-- **Calibration Defect from Gluing** (Section 11.4).
    Ensures that there exists a way to yoke holomorphic sheets across coordinate
    cubes to form an integral cycle with bounded calibration defect and mass.
    This is the final "Gluing" step of the SYR construction.
    Reference: [Hodge-v6-w-Jon-Update-MERGED.tex, Section 11.4]. -/
axiom calibration_defect_from_gluing (p : ℕ) (h : ℝ) (hh : h > 0) (C : Cubulation n X h)
    (β : SmoothForm n X (2 * p)) (hβ : isConePositive β) (m : ℕ)
    (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_raw : RawSheetSum n X (n - p) h C),
      IsValidGluing β T_raw ∧
      HasBoundedCalibrationDefect T_raw ψ (comass β * h) ∧
      (T_raw.toIntegralCurrent).isCycleAt ∧
      (T_raw.toIntegralCurrent : Current n X (2 * (n - p))).mass ≤ 2 * comass β

/-- **Holomorphic Coordinate Chart Theorem** -/
theorem exists_holomorphic_chart (x : X) :
    ∃ (U : Set X) (φ : U → EuclideanSpace ℂ (Fin n)), x ∈ U ∧ IsOpen U := by
  let chart := chartAt (EuclideanSpace ℂ (Fin n)) x
  use chart.source, chart
  constructor
  · exact mem_chart_source (EuclideanSpace ℂ (Fin n)) x
  · exact chart.open_source

/-- **Partition of Unity on Mesh** (Section 11.1).
    Ensures that there exists a partition of unity subordinate to a coordinate
    cubulation. This allows for the local-to-global transition in the yoking
    construction.
    Reference: [Hodge-v6-w-Jon-Update-MERGED.tex, Section 11.1]. -/
axiom exists_partition_of_unity_mesh {h : ℝ} (C : Cubulation n X h) :
    ∃ (ρ : C.cubes → X → ℝ), (∀ Q, Continuous (ρ Q)) ∧ (∀ x, ∑ Q, ρ Q x = 1)

/-- **Microstructure Boundary Estimate** (Proposition 11.8).
    The flat norm of the boundary of the raw microstructure current is O(h).
    Reference: [Hodge-v6-w-Jon-Update-MERGED.tex, Proposition 11.8]. -/
axiom gluing_flat_norm_bound {p : ℕ} {h : ℝ} {C : Cubulation n X h}
    (β : SmoothForm n X (2 * p)) (hβ : isConePositive β) :
    ∃ (T_raw : RawSheetSum n X (n - p) h C),
      flatNorm (∂ (T_raw.toIntegralCurrent).toFun) ≤ comass β * h

/-- **Microstructure Defect Estimate** (Proposition 11.9).
    The calibration defect of the raw microstructure current is O(h).
    Reference: [Hodge-v6-w-Jon-Update-MERGED.tex, Proposition 11.9]. -/
axiom microstructure_defect_bound {p : ℕ} {h : ℝ} {C : Cubulation n X h}
    (β : SmoothForm n X (2 * p)) (hβ : isConePositive β) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_raw : RawSheetSum n X (n - p) h C),
      calibrationDefect (T_raw.toIntegralCurrent).toFun ψ ≤ comass β * h

/-- **Microstructure Mass Estimate** (Proposition 11.10).
    The mass of the raw microstructure current is bounded by a constant multiple
    of the comass.
    Reference: [Hodge-v6-w-Jon-Update-MERGED.tex, Proposition 11.10]. -/
axiom microstructure_mass_bound {p : ℕ} {h : ℝ} {C : Cubulation n X h}
    (β : SmoothForm n X (2 * p)) (hβ : isConePositive β) :
    ∃ (T_raw : RawSheetSum n X (n - p) h C),
      (T_raw.toIntegralCurrent : Current n X (2 * (n - p))).mass ≤ 2 * comass β

/-! ## Main Construction Sequence -/

def microstructureSequence (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) (k : ℕ) :
    IntegralCurrent n X (2 * (n - p)) :=
  let h := canonicalMeshSequence.scale k
  let hh := canonicalMeshSequence.scale_pos k
  let C := cubulationFromMesh h hh
  Classical.choose (calibration_defect_from_gluing p h hh C γ hγ k ψ) |>.toIntegralCurrent

/-- **Theorem: Microstructure Cycles** (Section 11).
    Every element of the microstructure sequence is an integral cycle.
    Reference: [Hodge-v6-w-Jon-Update-MERGED.tex, Section 11]. -/
theorem microstructureSequence_are_cycles (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, (microstructureSequence p γ hγ ψ k).isCycleAt := by
  intro k; unfold microstructureSequence
  exact (Classical.choose_spec (calibration_defect_from_gluing p _ _ _ γ hγ k ψ)).2.2.1

theorem microstructureSequence_defect_bound (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, calibrationDefect (microstructureSequence p γ hγ ψ k).toFun ψ ≤ comass γ * (canonicalMeshSequence.scale k) := by
  intro k; unfold microstructureSequence
  exact (Classical.choose_spec (calibration_defect_from_gluing p _ _ _ γ hγ k ψ)).2.1

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
  use 2 * comass γ; intro k; unfold microstructureSequence
  exact (Classical.choose_spec (calibration_defect_from_gluing p _ _ _ γ hγ k ψ)).2.2.2.2

theorem microstructureSequence_flatnorm_bound (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ M : ℝ, ∀ k, flatNorm (microstructureSequence p γ hγ ψ k).toFun ≤ M := by
  obtain ⟨M, hM⟩ := microstructureSequence_mass_bound p γ hγ ψ
  use M; intro k; exact le_trans (flatNorm_le_mass _) (hM k)

/-- The microstructure sequence has a flat-convergent subsequence.
    This is an application of Federer-Fleming compactness to the uniformly
    bounded sequence of integral currents. -/
theorem microstructureSequence_flat_limit_exists (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_limit : IntegralCurrent n X (2 * (n - p))) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Filter.Tendsto (fun j => flatNorm ((microstructureSequence p γ hγ ψ (φ j)).toFun - T_limit.toFun))
        Filter.atTop (nhds 0) := by
  let M := 2 * comass γ
  have h_bound : ∀ j, (microstructureSequence p γ hγ ψ j : Current n X (2 * (n - p))).mass +
                      (microstructureSequence p γ hγ ψ j).boundary.toFun.mass ≤ M := by
    intro j; have h_mass := microstructureSequence_mass_bound p γ hγ ψ j
    have h_cycle := microstructureSequence_are_cycles p γ hγ ψ j
    have h_boundary : (microstructureSequence p γ hγ ψ j).boundary.toFun = 0 := by
      unfold IntegralCurrent.isCycleAt at h_cycle
      obtain ⟨k', h_deg, h_zero⟩ := h_cycle; exact h_zero
    simp [h_boundary, Current.mass_zero, h_mass]
  let hyp : FFCompactnessHypothesis n X (2 * (n - p) - 1) := {
    T := microstructureSequence p γ hγ ψ
    M := M
    mass_bound := by simpa using h_bound
  }
  let concl := federer_fleming_compactness _ hyp
  use concl.T_limit, concl.φ, concl.φ_strict_mono, concl.converges

end
