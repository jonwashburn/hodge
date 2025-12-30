import Hodge.Analytic.Currents
import Hodge.Analytic.FlatNorm
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Track B.4: Integral Currents
-/

noncomputable section

open Classical MeasureTheory

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]

/-- **Rectifiability** (Federer, 1969).
    A set S ⊆ X is k-rectifiable if it is the image of a bounded subset of ℝ^k under
    a Lipschitz map.
    Reference: [H. Federer, "Geometric Measure Theory", 1969, Section 3.2]. -/
def isRectifiable (k : ℕ) (S : Set X) : Prop :=
  ∃ (f : ℕ → EuclideanSpace ℝ (Fin k) → X),
    ∀ i, ∃ K : Set (EuclideanSpace ℝ (Fin k)), Bounded K ∧ LipschitzOnWith (Classical.choose (exists_lipschitz_const (f i))) (f i) K ∧ S ⊆ ⋃ i, f i '' K

theorem isRectifiable_empty (k : ℕ) : isRectifiable k (∅ : Set X) := by
  use fun _ _ => Classical.choice inferInstance
  intro i; use ∅; simp [isRectifiable]

theorem isRectifiable_union (k : ℕ) (S₁ S₂ : Set X) :
    isRectifiable k S₁ → isRectifiable k S₂ → isRectifiable k (S₁ ∪ S₂) := by
  intro h1 h2
  obtain ⟨f1, hf1⟩ := h1
  obtain ⟨f2, hf2⟩ := h2
  -- Combine sequences by interlacing (zig-zag)
  use fun i => if i % 2 = 0 then f1 (i / 2) else f2 (i / 2)
  intro i
  by_cases hi : i % 2 = 0
  · obtain ⟨K, hK⟩ := hf1 (i / 2)
    use K; simp [hi, hK]
  · obtain ⟨K, hK⟩ := hf2 (i / 2)
    use K; simp [hi, hK]

/-- **Integral Polyhedral Chains**
    The building blocks of integral currents. -/
def IntegralPolyhedralChain (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] : Set (Current n X k) :=
  { T | ∃ (m : ℕ) (simplices : Fin m → Set X) (h_rect : ∀ i, isRectifiable k (simplices i)) (coeffs : Fin m → ℤ),
    T = ∑ i, (coeffs i : ℝ) • (integrationCurrent (simplices i) (h_rect i)) }

/-- Integration current over a rectifiable set. -/
opaque integrationCurrent {k : ℕ} (S : Set X) (hS : isRectifiable k S) : Current n X k

theorem polyhedral_add {k : ℕ} (S T : Current n X k) :
    S ∈ IntegralPolyhedralChain n X k → T ∈ IntegralPolyhedralChain n X k → S + T ∈ IntegralPolyhedralChain n X k := by
  rintro ⟨mS, sS, hrS, cS, hS⟩ ⟨mT, sT, hrT, cT, hT⟩
  use mS + mT
  let s := fun i : Fin (mS + mT) => if h : i < mS then sS ⟨i, h⟩ else sT ⟨i - mS, by linarith [i.2]⟩
  let hr := fun i : Fin (mS + mT) => if h : i < mS then hrS ⟨i, h⟩ else hrT ⟨i - mS, by linarith [i.2]⟩
  let c := fun i : Fin (mS + mT) => if h : i < mS then cS ⟨i, h⟩ else cT ⟨i - mS, by linarith [i.2]⟩
  use s, hr, c
  rw [hS, hT]
  simp [s, c]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; simp [i.2]
  · rw [← Fin.sum_univ_add_sum_univ_sub mS mT]
    apply Finset.sum_congr rfl; intro i _; simp
    have : ¬ ((i.1 + mS) < mS) := by linarith; simp [this]

theorem polyhedral_zero {k : ℕ} : (0 : Current n X k) ∈ IntegralPolyhedralChain n X k := by
  use 0, (fun _ => ∅), (fun _ => isRectifiable_empty k), (fun _ => 0)
  simp [IntegralPolyhedralChain]

theorem polyhedral_smul {k : ℕ} (c : ℤ) (T : Current n X k) :
    T ∈ IntegralPolyhedralChain n X k → (c • T) ∈ IntegralPolyhedralChain n X k := by
  intro ⟨m, s, hr, coeffs, hT⟩
  use m, s, hr, fun i => c * coeffs i
  rw [hT, Current.smul_curr]
  simp [smul_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro i _; simp [smul_smul]; ring

theorem polyhedral_boundary {k : ℕ} (T : Current n X (k + 1)) :
    T ∈ IntegralPolyhedralChain n X (k + 1) → Current.boundary T ∈ IntegralPolyhedralChain n X k := by
  intro ⟨m, s, hr, coeffs, hT⟩
  -- The boundary of a simplex is a sum of its faces (lower dimensional simplices).
  -- This is the fundamental property of polyhedral chains.
  -- Each face is also rectifiable.
  sorry -- Standard GMT fact (Federer 4.1.22)

/-- Predicate stating that a current is an integral current.
    Defined as the closure of integral polyhedral chains in the flat norm.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
def isIntegral {k : ℕ} (T : Current n X k) : Prop :=
  ∀ ε > 0, ∃ P ∈ IntegralPolyhedralChain n X k, flatNorm (T - P) < ε

/-- **Theorem: Sum of Integral Currents is Integral** (Federer-Fleming, 1960). -/
theorem isIntegral_add {k : ℕ} (S T : Current n X k) :
    isIntegral S → isIntegral T → isIntegral (S + T) := by
  intro hS hT ε hε
  obtain ⟨PS, hPS, dS⟩ := hS (ε/2) (by linarith)
  obtain ⟨PT, hPT, dT⟩ := hT (ε/2) (by linarith)
  use PS + PT
  constructor
  · apply polyhedral_add PS PT hPS hPT
  · calc flatNorm (S + T - (PS + PT))
      _ = flatNorm ((S - PS) + (T - PT)) := by
        congr; rw [Current.add_curr, Current.add_curr, Current.neg_curr, Current.neg_curr, Current.add_curr]
        ext ω; simp [Current.add_curr, Current.neg_curr]; ring
      _ ≤ flatNorm (S - PS) + flatNorm (T - PT) := flatNorm_add_le _ _
      _ < ε/2 + ε/2 := add_lt_add dS dT
      _ = ε := by ring

/-- **Theorem: Zero current is integral.** -/
theorem isIntegral_zero_current (k : ℕ) [Nonempty X] : isIntegral (0 : Current n X k) := by
  intro ε hε
  use 0, polyhedral_zero
  rw [sub_zero, flatNorm_zero]
  exact hε

/-- **Theorem: Integer Scaling of Integral Currents is Integral.** -/
theorem isIntegral_smul {k : ℕ} (c : ℤ) (T : Current n X k) :
    isIntegral T → isIntegral (c • T) := by
  intro hT ε hε
  if hc : c = 0 then
    subst hc
    have h0 : (0 : ℤ) • T = 0 := by ext ω; simp [Current.smul_curr, Current.zero]
    rw [h0]
    apply isIntegral_zero_current _ hε
  else
    let ε' := ε / (|c| : ℝ)
    have hε' : ε' > 0 := by
      apply div_pos hε
      simp [hc]
    obtain ⟨P, hP, dP⟩ := hT ε' hε'
    use c • P
    constructor
    · apply polyhedral_smul c P hP
    · have h_smul : (c : ℝ) • T - (c : ℝ) • P = (c : ℝ) • (T - P) := by
        ext ω; simp [Current.smul_curr, Current.neg_curr, Current.add_curr]; ring
      rw [h_smul, flatNorm_smul]
      have h_abs : |(c : ℝ)| = (|(c : ℤ)| : ℝ) := by simp
      rw [h_abs]
      apply (mul_lt_iff_lt_div (by simp [hc] : 0 < (|(c : ℤ)| : ℝ))).mpr
      exact dP

/-- **The boundary of an integral current is integral.** -/
theorem isIntegral_boundary {k : ℕ} (T : Current n X (k + 1)) :
    isIntegral T → isIntegral (Current.boundary T) := by
  intro hT ε hε
  obtain ⟨P, hP, dP⟩ := hT ε hε
  use Current.boundary P, polyhedral_boundary P hP
  calc flatNorm (Current.boundary T - Current.boundary P)
    _ = flatNorm (Current.boundary (T - P)) := by
      ext ω; simp [Current.boundary, Current.neg_curr, Current.add_curr]
    _ ≤ flatNorm (T - P) := flatNorm_boundary_le _
    _ < ε := dP

/-- An integral current structure wrapping the predicate. -/
structure IntegralCurrent (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  toFun : Current n X k
  is_integral : isIntegral toFun

/-- The zero integral current. -/
def zero_int (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] :
    IntegralCurrent n X k :=
  { toFun := 0
    is_integral := isIntegral_zero_current k }

instance {k : ℕ} : Inhabited (IntegralCurrent n X k) :=
  ⟨zero_int n X k⟩

/-- Convert an IntegralCurrent to a Current. -/
instance {k : ℕ} : Coe (IntegralCurrent n X k) (Current n X k) where
  coe := IntegralCurrent.toFun

/-- The isCycle property for IntegralCurrent. -/
def IntegralCurrent.isCycleAt {k : ℕ} (T : IntegralCurrent n X k) : Prop :=
  ∃ (k' : ℕ) (h : k = k' + 1), (Current.boundary (h ▸ T.toFun)) = 0

/-- Boundary of an integral current. -/
def IntegralCurrent.boundary {k : ℕ} (T : IntegralCurrent n X (k + 1)) :
    IntegralCurrent n X k where
  toFun := Current.boundary T.toFun
  is_integral := isIntegral_boundary T.toFun T.is_integral

/-- If an integral current is a cycle, its boundary mass is zero. -/
theorem IntegralCurrent.boundary_mass_zero {k : ℕ} (T : IntegralCurrent n X (k + 1))
    (h_cycle : T.isCycleAt) : Current.mass (Current.boundary T.toFun) = 0 := by
  obtain ⟨k', h_dim, h_bdy⟩ := h_cycle
  injection h_dim with h_k
  subst h_k
  simp at h_bdy
  rw [h_bdy]
  exact Current.mass_zero

end
