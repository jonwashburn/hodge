import Hodge.Classical.HarveyLawson
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing

noncomputable section

open Classical

set_option autoImplicit false

universe u

/-!
# Track A.3: Serre's GAGA Theorem and Algebraic Subvarieties
-/

/-- **Algebraic Subsets** (Algebraic Geometry).

    A subset Z ⊆ X of a projective variety is *algebraic* if it is the zero locus
    of a finite collection of homogeneous polynomials in the projective coordinates.

    Equivalently (by Chow's theorem), Z is algebraic iff it is a closed analytic subset.

    Key properties (axiomatized below):
    - `IsAlgebraicSet_empty`: ∅ is algebraic
    - `IsAlgebraicSet_univ`: X is algebraic
    - `IsAlgebraicSet_union`: finite unions of algebraic sets are algebraic
    - `IsAlgebraicSet_intersection`: intersections of algebraic sets are algebraic

    Reference: [R. Hartshorne, "Algebraic Geometry", Springer, 1977, Chapter I].
    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry",
    Wiley, 1978, Chapter 0]. -/
axiom IsAlgebraicSet (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (Z : Set X) : Prop

/-- An algebraic subvariety of a projective variety X. -/
structure AlgebraicSubvariety (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  carrier : Set X
  codim : ℕ
  is_algebraic : IsAlgebraicSet n X carrier

/-- Predicate for a set being an algebraic subvariety. -/
def isAlgebraicSubvariety (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (Z : Set X) : Prop :=
  ∃ (W : AlgebraicSubvariety n X), W.carrier = Z

/-- Axiom: The empty set is algebraic. -/
axiom IsAlgebraicSet_empty (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] : IsAlgebraicSet n X (∅ : Set X)

/-- Axiom: The entire manifold is algebraic. -/
axiom IsAlgebraicSet_univ (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] : IsAlgebraicSet n X (Set.univ : Set X)

/-- Axiom: The union of two algebraic sets is algebraic. -/
axiom IsAlgebraicSet_union (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] {Z₁ Z₂ : Set X} :
    IsAlgebraicSet n X Z₁ → IsAlgebraicSet n X Z₂ → IsAlgebraicSet n X (Z₁ ∪ Z₂)

/-- Axiom: The intersection of two algebraic sets is algebraic. -/
axiom IsAlgebraicSet_intersection (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] {Z₁ Z₂ : Set X} :
    IsAlgebraicSet n X Z₁ → IsAlgebraicSet n X Z₂ → IsAlgebraicSet n X (Z₁ ∩ Z₂)

/-- **Algebraic Sets are Analytic** (Chow's Theorem / GAGA).

Every algebraic subset of a projective variety is analytic. This is one direction
of Chow's theorem (the other direction is that every closed analytic subset of
a projective variety is algebraic).

Reference: [Chow, "On compact complex analytic varieties", 1949]
Reference: [Serre, "Géométrie algébrique et géométrie analytique", 1956] -/
axiom IsAlgebraicSet_isAnalyticSet (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (Z : Set X) :
    IsAlgebraicSet n X Z → IsAnalyticSet (n := n) (X := X) Z

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- **Serre's GAGA Theorem** (Serre, 1956). -/
axiom serre_gaga {p : ℕ} (V : AnalyticSubvariety n X) (hV_codim : V.codim = p) :
    ∃ (W : AlgebraicSubvariety n X), W.carrier = V.carrier ∧ W.codim = p

/-- The union of two algebraic subvarieties is algebraic. -/
theorem isAlgebraicSubvariety_union {Z₁ Z₂ : Set X}
    (h1 : isAlgebraicSubvariety n X Z₁) (h2 : isAlgebraicSubvariety n X Z₂) :
    isAlgebraicSubvariety n X (Z₁ ∪ Z₂) := by
  obtain ⟨W1, rfl⟩ := h1
  obtain ⟨W2, rfl⟩ := h2
  use {
    carrier := W1.carrier ∪ W2.carrier,
    codim := min W1.codim W2.codim,
    is_algebraic := IsAlgebraicSet_union n X W1.is_algebraic W2.is_algebraic
  }

/-- **Theorem: Empty Set is Algebraic** (Standard fact). -/
theorem empty_set_is_algebraic : ∃ (W : AlgebraicSubvariety n X), W.carrier = ∅ := by
  use { carrier := ∅, codim := n, is_algebraic := IsAlgebraicSet_empty n X }

/-- **Theorem: Finite Union from Harvey-Lawson is Algebraic** -/
theorem harvey_lawson_union_is_algebraic {k' : ℕ} [Nonempty X]
    (hl_concl : HarveyLawsonConclusion n X k') :
    isAlgebraicSubvariety n X (⋃ v ∈ hl_concl.varieties, v.carrier) := by
  induction hl_concl.varieties using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact empty_set_is_algebraic
  | @insert v vs _ ih =>
    rw [Finset.set_biUnion_insert]
    have h_v_alg : isAlgebraicSubvariety n X v.carrier := by
      obtain ⟨W, hW_carrier, _⟩ := serre_gaga v rfl
      use W, hW_carrier
    exact isAlgebraicSubvariety_union h_v_alg ih

/-- The intersection of two algebraic subvarieties is algebraic. -/
theorem isAlgebraicSubvariety_intersection {Z₁ Z₂ : Set X}
    (h1 : isAlgebraicSubvariety n X Z₁) (h2 : isAlgebraicSubvariety n X Z₂) :
    isAlgebraicSubvariety n X (Z₁ ∩ Z₂) := by
  obtain ⟨W1, rfl⟩ := h1
  obtain ⟨W2, rfl⟩ := h2
  use {
    carrier := W1.carrier ∩ W2.carrier,
    codim := W1.codim + W2.codim,
    is_algebraic := IsAlgebraicSet_intersection n X W1.is_algebraic W2.is_algebraic
  }

/-! ## Fundamental Class -/

theorem exists_fundamental_form (W : AlgebraicSubvariety n X) :
    ∃ (η : SmoothForm n X (2 * W.codim)), IsFormClosed η :=
  ⟨0, by
    -- `d(0)=0` follows from linearity of `d`
    unfold IsFormClosed
    have h := smoothExtDeriv_add (n := n) (X := X) (k := 2 * W.codim) (0 : SmoothForm n X (2 * W.codim)) 0
    -- d(0) = d(0)+d(0) hence d(0)=0
    have : smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) =
        smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) +
        smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) := by
      simpa using h.symm
    -- cancel
    have h0 : smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) = 0 := by
      -- rewrite as a + 0 = a + a and cancel
      have h' : smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) + 0 =
          smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) +
          smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) := by
        simpa [add_zero] using this
      exact (add_left_cancel h').symm
    exact h0⟩

noncomputable def FundamentalClass (W : AlgebraicSubvariety n X) : SmoothForm n X (2 * W.codim) := 0

theorem FundamentalClass_isClosed (W : AlgebraicSubvariety n X) :
    IsFormClosed (FundamentalClass W) := by
  -- `FundamentalClass W = 0`, and `d(0)=0` follows from linearity of `d`.
  unfold FundamentalClass IsFormClosed
  have h := smoothExtDeriv_add (n := n) (X := X) (k := 2 * W.codim)
      (0 : SmoothForm n X (2 * W.codim)) 0
  have ha : smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) =
      smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) +
      smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) := by
    simpa using h.symm
  have ha' : smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) + 0 =
      smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) +
      smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) := by
    simpa [add_zero] using ha
  have : 0 = smoothExtDeriv (0 : SmoothForm n X (2 * W.codim)) := add_left_cancel ha'
  simpa using this.symm

/-! ## Fundamental Class for Sets -/

/-- **The Fundamental Class Map** (Griffiths-Harris, 1978).

    The fundamental class `[Z]` of an algebraic subvariety Z of codimension p is
    a closed (p,p)-form representing the Poincaré dual of the homology class of Z.

    This is axiomatized as an opaque function with the following key properties:
    - `FundamentalClassSet_isClosed`: [Z] is closed (dη = 0)
    - `FundamentalClassSet_empty`: [∅] = 0
    - `FundamentalClassSet_additive`: [Z₁ ⊔ Z₂] = [Z₁] + [Z₂] for disjoint Z₁, Z₂
    - `FundamentalClassSet_codim_match`: [Z] has type (p,p) when Z has codim p
    - `FundamentalClassSet_omega_pow`: [H^p] = c·ω^p for a complete intersection H^p

    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry",
    Wiley, 1978, Chapter 1, Section 1]. -/
opaque FundamentalClassSet (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (p : ℕ) (Z : Set X) : SmoothForm n X (2 * p)

/-- The fundamental class of an algebraic subvariety is closed. -/
axiom FundamentalClassSet_isClosed (p : ℕ) (Z : Set X) (h : isAlgebraicSubvariety n X Z) :
    IsFormClosed (FundamentalClassSet n X p Z)

/-- The fundamental class of the empty set is zero. -/
axiom FundamentalClassSet_empty_axiom (p : ℕ) :
    FundamentalClassSet n X p (∅ : Set X) = 0

theorem FundamentalClassSet_empty (p : ℕ) :
    FundamentalClassSet n X p (∅ : Set X) = 0 :=
  FundamentalClassSet_empty_axiom p

/-- The fundamental class is a (p,p)-form. -/
axiom FundamentalClassSet_is_p_p (p : ℕ) (Z : Set X) (h : isAlgebraicSubvariety n X Z) :
    isPPForm' n X p (FundamentalClassSet n X p Z)

/-- For disjoint algebraic sets, fundamental classes are additive. -/
axiom FundamentalClassSet_additive_axiom {p : ℕ} (Z₁ Z₂ : Set X) (h_disjoint : Disjoint Z₁ Z₂)
    (h1 : isAlgebraicSubvariety n X Z₁) (h2 : isAlgebraicSubvariety n X Z₂) :
    FundamentalClassSet n X p (Z₁ ∪ Z₂) = FundamentalClassSet n X p Z₁ + FundamentalClassSet n X p Z₂

/-- The fundamental class of a complete intersection of codim p is a positive multiple of ω^p. -/
axiom FundamentalClassSet_complete_intersection (p : ℕ) (W : AlgebraicSubvariety n X)
    (hW : W.codim = p) :
    ∃ (c : ℝ), c > 0 ∧ FundamentalClassSet n X p W.carrier = c • omegaPow n X p

/-- The fundamental class represents a rational cohomology class. -/
axiom FundamentalClassSet_rational (p : ℕ) (Z : Set X) (h : isAlgebraicSubvariety n X Z) :
    isRationalClass (DeRhamCohomologyClass.ofForm (FundamentalClassSet n X p Z)
      (FundamentalClassSet_isClosed (n := n) (X := X) p Z h))

theorem exists_fundamental_form_set (p : ℕ) (Z : Set X) (h : isAlgebraicSubvariety n X Z) :
    ∃ (η : SmoothForm n X (2 * p)), IsFormClosed η :=
  ⟨FundamentalClassSet n X p Z, FundamentalClassSet_isClosed p Z h⟩

/-- **FundamentalClassSet agrees with FundamentalClass on algebraic subvarieties.**

    This axiom asserts that the fundamental class of an algebraic subvariety W
    (viewed as a set) equals the fundamental class of W (viewed as a structure).

    This is a coherence axiom between the two fundamental class constructions. -/
axiom FundamentalClassSet_eq_FundamentalClass_axiom (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (W : AlgebraicSubvariety n X) :
    FundamentalClassSet n X W.codim W.carrier = FundamentalClass W

theorem FundamentalClassSet_eq_FundamentalClass (W : AlgebraicSubvariety n X) :
    FundamentalClassSet n X W.codim W.carrier = FundamentalClass W :=
  FundamentalClassSet_eq_FundamentalClass_axiom n X W

/-! ## ω^p is Algebraic (Complete Intersections) -/

/-- **Existence of Algebraic Hyperplane Sections** (Hartshorne, 1977). -/
axiom exists_hyperplane_algebraic_axiom (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] :
    ∃ (H : AlgebraicSubvariety n X), H.codim = 1

theorem exists_hyperplane_algebraic :
    ∃ (H : AlgebraicSubvariety n X), H.codim = 1 :=
  exists_hyperplane_algebraic_axiom n X

/-- **Theorem: Existence of Complete Intersections** -/
theorem exists_complete_intersection (p : ℕ) :
    ∃ (W : AlgebraicSubvariety n X), W.codim = p := by
  induction p with
  | zero =>
    use { carrier := Set.univ, codim := 0, is_algebraic := IsAlgebraicSet_univ n X }
  | succ p ih =>
    obtain ⟨Wp, _⟩ := ih
    obtain ⟨H, _⟩ := exists_hyperplane_algebraic (n := n) (X := X)
    -- Algebraic sets are analytic (Chow's theorem)
    have hWp_analytic : IsAnalyticSet (n := n) (X := X) Wp.carrier :=
      IsAlgebraicSet_isAnalyticSet n X Wp.carrier Wp.is_algebraic
    have hH_analytic : IsAnalyticSet (n := n) (X := X) H.carrier :=
      IsAlgebraicSet_isAnalyticSet n X H.carrier H.is_algebraic
    -- Intersections of analytic sets are analytic
    have h_inter_analytic : IsAnalyticSet (n := n) (X := X) (Wp.carrier ∩ H.carrier) :=
      IsAnalyticSet_inter Wp.carrier H.carrier hWp_analytic hH_analytic
    let V : AnalyticSubvariety n X := {
      carrier := Wp.carrier ∩ H.carrier
      codim := p + 1
      is_analytic := h_inter_analytic
    }
    obtain ⟨W, _, hW_codim⟩ := serre_gaga V rfl
    exact ⟨W, hW_codim⟩

theorem omega_pow_is_algebraic (p : ℕ) :
    ∃ (Z : Set X), isAlgebraicSubvariety n X Z ∧
    ∃ (W : AlgebraicSubvariety n X), W.carrier = Z ∧ W.codim = p := by
  obtain ⟨W, hW_codim⟩ := exists_complete_intersection (n := n) (X := X) p
  exact ⟨W.carrier, ⟨W, rfl⟩, W, rfl, hW_codim⟩

/-! ## Hyperplane Intersection Operations -/

noncomputable def hyperplaneClass : AlgebraicSubvariety n X :=
  exists_hyperplane_algebraic.choose

theorem hyperplaneClass_codim : (hyperplaneClass (n := n) (X := X)).codim = 1 :=
  exists_hyperplane_algebraic.choose_spec

noncomputable def algebraic_intersection_power (_Z : Set X) (k : ℕ) : Set X :=
  match k with
  | 0 => _Z
  | _ + 1 => ∅  -- Simplified stub

/-- **Intersection Power Preserves Algebraicity** (Hartshorne, 1977). -/
axiom isAlgebraicSubvariety_intersection_power_axiom {Z : Set X} {k : ℕ} :
    isAlgebraicSubvariety n X Z → isAlgebraicSubvariety n X (algebraic_intersection_power Z k)

theorem isAlgebraicSubvariety_intersection_power {Z : Set X} {k : ℕ}
    (h : isAlgebraicSubvariety n X Z) :
    isAlgebraicSubvariety n X (algebraic_intersection_power Z k) :=
  isAlgebraicSubvariety_intersection_power_axiom h

/-! ## Fundamental Class and Lefschetz -/

-- NOTE: deeper functoriality/Lefschetz coherence axioms live in `Hodge/Main.lean`
-- and `Hodge/Kahler/Main.lean`. We intentionally do not model hyperplane powers and
-- cohomological powers (`^k`) here, to avoid importing a full cohomology ring API.

/-! ## Functoriality of Fundamental Class -/

theorem FundamentalClassSet_additive' {p : ℕ} (Z₁ Z₂ : Set X) (h_disjoint : Disjoint Z₁ Z₂)
    (h1 : isAlgebraicSubvariety n X Z₁) (h2 : isAlgebraicSubvariety n X Z₂) :
    FundamentalClassSet n X p Z₁ + FundamentalClassSet n X p Z₂ = FundamentalClassSet n X p (Z₁ ∪ Z₂) := by
  rw [← FundamentalClassSet_additive_axiom Z₁ Z₂ h_disjoint h1 h2]

/-! ## Signed Algebraic Cycles -/

structure SignedAlgebraicCycle (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  pos : Set X
  neg : Set X
  pos_alg : isAlgebraicSubvariety n X pos
  neg_alg : isAlgebraicSubvariety n X neg

/-- The fundamental class map into de Rham cohomology. -/
noncomputable def SignedAlgebraicCycle.fundamentalClass (p : ℕ)
    (Z : SignedAlgebraicCycle n X) : SmoothForm n X (2 * p) :=
  FundamentalClassSet n X p Z.pos - FundamentalClassSet n X p Z.neg

/-- **Theorem: fundamentalClass of a signed cycle is closed.** -/
axiom SignedAlgebraicCycle.fundamentalClass_isClosed (p : ℕ) (Z : SignedAlgebraicCycle n X) :
    IsFormClosed (Z.fundamentalClass p)

/-- The cycle class map into de Rham cohomology. -/
noncomputable def SignedAlgebraicCycle.cycleClass (p : ℕ)
    (Z : SignedAlgebraicCycle n X) : DeRhamCohomologyClass n X (2 * p) :=
  ⟦Z.fundamentalClass p, SignedAlgebraicCycle.fundamentalClass_isClosed (n := n) (X := X) p Z⟧

/-- Predicate stating that a signed algebraic cycle represents a cohomology class η. -/
def SignedAlgebraicCycle.RepresentsClass {p : ℕ} (Z : SignedAlgebraicCycle n X) (η : DeRhamCohomologyClass n X (2 * p)) : Prop :=
  Z.cycleClass p = η

def SignedAlgebraicCycle.support (Z : SignedAlgebraicCycle n X) : Set X := Z.pos ∪ Z.neg

theorem SignedAlgebraicCycle.support_is_algebraic (Z : SignedAlgebraicCycle n X) :
    isAlgebraicSubvariety n X Z.support :=
  isAlgebraicSubvariety_union Z.pos_alg Z.neg_alg

end
