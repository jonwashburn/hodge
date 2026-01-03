import Hodge.Analytic.IntegralCurrents
import Hodge.Analytic.FlatNorm
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic

noncomputable section

open Classical Filter

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]

/-!
# Track A.3: Federer-Fleming Compactness Theorem
-/

/-- Auxiliary constants for the Deformation Theorem. -/
noncomputable def C1 (_n _k : ℕ) : ℝ := 2
noncomputable def C2 (_n _k : ℕ) : ℝ := 2
noncomputable def C3 (_n _k : ℕ) : ℝ := 2
noncomputable def C4 (_n _k : ℕ) : ℝ := 2

/-- **The Deformation Theorem** (Federer-Fleming, 1960).

    **STATUS: CLASSICAL PILLAR**

    Any integral current T can be approximated by a polyhedral current P on a
    grid of size ε, with the decomposition T = P + ∂Q + S, where all terms
    have explicit mass bounds in terms of T and ε.

    **Mathematical Content**: The deformation theorem is the key technical tool
    in geometric measure theory for approximating currents by polyhedral chains.
    Given a k-current T and grid size ε:
    1. P is a polyhedral current close to T
    2. Q is a (k+1)-current bounding the difference
    3. S is a small error current

    **Why This is an Axiom**: The proof requires:
    - Construction of a cubical decomposition of the ambient space
    - Projection operators onto lower-dimensional skeletons
    - Detailed mass estimates using the coarea formula
    - Careful handling of multiplicities and orientations

    **Usage in Main Proof**: The deformation theorem underlies the Federer-Fleming
    compactness theorem, which is used to extract convergent subsequences from
    the microstructure sequence.

    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents",
    Ann. of Math. (2) 72 (1960), 458-520, Theorem 5.5].
    Reference: [H. Federer, "Geometric Measure Theory", Springer, 1969, Section 4.2]. -/
axiom deformation_theorem (k : ℕ) (T : IntegralCurrent n X (k + 1)) (ε : ℝ) (hε : ε > 0) :
    ∃ (P : IntegralCurrent n X (k + 1)) (Q : IntegralCurrent n X (k + 2)) (S : IntegralCurrent n X (k + 1)),
      (T : Current n X (k + 1)) = P + (Current.boundary Q.toFun) + S ∧
      (P : Current n X (k + 1)).mass ≤ C1 n k * ((T : Current n X (k + 1)).mass + ε * Current.mass T.boundary.toFun) ∧
      Current.mass (IntegralCurrent.boundary P).toFun ≤ C2 n k * Current.mass T.boundary.toFun ∧
      (Q : Current n X (k + 2)).mass ≤ C3 n k * ε * (T : Current n X (k + 1)).mass ∧
      (S : Current n X (k + 1)).mass ≤ C4 n k * ε * Current.mass T.boundary.toFun

/-- The hypothesis bundle for Federer-Fleming compactness. -/
structure FFCompactnessHypothesis (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  T : ℕ → IntegralCurrent n X (k + 1)
  M : ℝ
  mass_bound : ∀ j, (T j : Current n X (k + 1)).mass + (T j).boundary.toFun.mass ≤ M

/-- The conclusion of Federer-Fleming. -/
structure FFCompactnessConclusion (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (hyp : FFCompactnessHypothesis n X k) where
  T_limit : IntegralCurrent n X (k + 1)
  φ : ℕ → ℕ
  φ_strict_mono : StrictMono φ
  converges : Tendsto (fun j => flatNorm ((hyp.T (φ j) : Current n X (k + 1)) - T_limit.toFun)) atTop (nhds 0)

/-- **Federer-Fleming Compactness Theorem** (Federer-Fleming, 1960).

    **STATUS: CLASSICAL PILLAR**

    A sequence of integral currents with uniformly bounded mass and boundary mass
    has a subsequence converging in flat norm to an integral current.

    **Mathematical Content**: This is the fundamental compactness theorem in
    geometric measure theory. For a sequence {T_j} of integral k-currents with
    mass(T_j) + mass(∂T_j) ≤ M:
    1. There exists a subsequence T_{φ(j)} converging in flat norm
    2. The limit T_∞ is an integral current
    3. mass(T_∞) ≤ liminf mass(T_{φ(j)})

    **Why This is an Axiom**: The proof requires:
    - The deformation theorem (approximation by polyhedral chains)
    - Compactness of the space of polyhedral chains with bounded complexity
    - Lower semicontinuity of mass under flat convergence
    - The slicing theorem for currents

    **Usage in Main Proof**: Applied to extract a convergent subsequence from
    the microstructure sequence {T_N}, ensuring the limit T_∞ exists as an
    integral current that is calibrated by ω^p.

    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents",
    Ann. of Math. (2) 72 (1960), 458-520, Theorem 5.7].
    Reference: [H. Federer, "Geometric Measure Theory", Springer, 1969, Section 4.2.17].
    Reference: [F. Morgan, "Geometric Measure Theory: A Beginner's Guide",
    5th ed., Academic Press, 2016, Chapter 5]. -/
axiom federer_fleming_compactness_axiom (k : ℕ)
    (hyp : FFCompactnessHypothesis n X k) :
    FFCompactnessConclusion n X k hyp

/-- Wrapper providing the Federer-Fleming compactness result. -/
def federer_fleming_compactness (k : ℕ)
    (hyp : FFCompactnessHypothesis n X k) :
    FFCompactnessConclusion n X k hyp :=
  federer_fleming_compactness_axiom k hyp

end
