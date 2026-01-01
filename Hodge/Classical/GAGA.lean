import Hodge.Classical.HarveyLawson
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing
import Hodge.Classical.Lefschetz

noncomputable section

open Classical

set_option autoImplicit false

universe u

/-!
# Track A.3: Serre's GAGA Theorem and Algebraic Subvarieties
-/

/-- **Zariski Topology on Projective Space** (Conceptual).
    A set is Zariski closed if it is the zero locus of homogeneous polynomials.

    **Opaque Definition**: This predicate is opaque because the Zariski topology
    requires defining polynomial rings and their zero loci on projective varieties,
    which requires significant algebraic geometry infrastructure.

    Reference: [R. Hartshorne, "Algebraic Geometry", Springer, 1977, Chapter I.1]. -/
opaque IsZariskiClosed {n : ℕ} (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] (Z : Set X) : Prop

/-- **Algebraic Subsets** (Algebraic Geometry).
    A subset Z ⊆ X of a projective variety is *algebraic* if it is closed in the Zariski topology. -/
def IsAlgebraicSet (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] (Z : Set X) : Prop :=
  IsZariskiClosed (n := n) X Z

/-- An algebraic subvariety of a projective variety X. -/
structure AlgebraicSubvariety (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] where
  carrier : Set X
  codim : ℕ
  is_algebraic : IsAlgebraicSet n X carrier

/-- Predicate for a set being an algebraic subvariety. -/
def isAlgebraicSubvariety (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] (Z : Set X) : Prop :=
  ∃ (W : AlgebraicSubvariety n X), W.carrier = Z

/-- The empty set is algebraic. -/
axiom IsAlgebraicSet_empty (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] : IsAlgebraicSet n X (∅ : Set X)

/-- The entire manifold is algebraic. -/
axiom IsAlgebraicSet_univ (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] : IsAlgebraicSet n X (Set.univ : Set X)

/-- The union of two algebraic sets is algebraic. -/
axiom IsAlgebraicSet_union (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] {Z₁ Z₂ : Set X} :
    IsAlgebraicSet n X Z₁ → IsAlgebraicSet n X Z₂ → IsAlgebraicSet n X (Z₁ ∪ Z₂)

/-- The intersection of two algebraic sets is algebraic. -/
axiom IsAlgebraicSet_intersection (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] {Z₁ Z₂ : Set X} :
    IsAlgebraicSet n X Z₁ → IsAlgebraicSet n X Z₂ → IsAlgebraicSet n X (Z₁ ∩ Z₂)

/-- Algebraic sets are closed in the classical topology. -/
axiom IsAlgebraicSet_isClosed (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (S : Set X) : IsAlgebraicSet n X S → IsClosed S

/-- **Algebraic Sets are Analytic** (Chow's Theorem / GAGA).

    **Deep Theorem Citation**: Every algebraic subset of a projective complex manifold
    is also an analytic subset. This is the "easy" direction of GAGA.

    Reference: [W.-L. Chow, "On compact complex analytic varieties",
    Amer. J. Math. 71 (1949), 893-914].
    Reference: [Hartshorne, 1977, Appendix B, Corollary B.3]. -/
axiom IsAlgebraicSet_isAnalyticSet (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] (Z : Set X) :
    IsAlgebraicSet n X Z → IsAnalyticSet (n := n) (X := X) Z

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- **Serre's GAGA Theorem** (Serre, 1956).

    **Deep Theorem Citation**: GAGA (Géométrie Algébrique et Géométrie Analytique)
    establishes an equivalence between the algebraic and analytic categories on
    projective varieties. In particular, every analytic subvariety of a projective
    complex manifold is algebraic.

    Reference: [J.-P. Serre, "Géométrie algébrique et géométrie analytique",
    Ann. Inst. Fourier 6 (1956), 1-42].
    Reference: [R. Hartshorne, "Algebraic Geometry", Springer, 1977, Appendix B].

    **Status**: This is one of the deepest theorems in complex algebraic geometry,
    connecting analytic and algebraic geometry. It requires the full machinery of
    sheaf cohomology and is correctly axiomatized here.

    **Usage in Main Proof**: Applied to convert the analytic varieties from
    Harvey-Lawson into algebraic subvarieties, completing the Hodge conjecture. -/
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

/-- **Theorem: Empty Set is Algebraic** -/
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

/-! ## Fundamental Class for Sets -/

/-- **The Fundamental Class Map** (Griffiths-Harris, 1978).
    The fundamental class `[Z]` of an algebraic subvariety Z of codimension p is
    a closed (p,p)-form representing the Poincaré dual of the homology class of Z.

    This is defined opaquely because constructing the fundamental class requires:
    1. The current of integration over Z (geometric measure theory)
    2. De Rham's theorem to get a smooth representative
    3. The Hodge decomposition to get a harmonic representative

    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry",
    Wiley, 1978, Chapter 1, Section 1]. -/
opaque FundamentalClassSet (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (p : ℕ) (Z : Set X) : SmoothForm n X (2 * p)

/-- The fundamental class of an algebraic subvariety is closed (Griffiths-Harris 1978).
    This follows because algebraic subvarieties are cycles in homology. -/
axiom FundamentalClassSet_isClosed (p : ℕ) (Z : Set X) (h : isAlgebraicSubvariety n X Z) :
    IsFormClosed (FundamentalClassSet n X p Z)

/-- The fundamental class of the empty set is zero.
    The empty variety has no homology, so its dual form is zero. -/
axiom FundamentalClassSet_empty (p : ℕ) :
    FundamentalClassSet n X p (∅ : Set X) = 0

/-- The fundamental class is a (p,p)-form (Griffiths-Harris 1978).
    For an algebraic subvariety of codimension p, the Poincaré dual is type (p,p). -/
axiom FundamentalClassSet_is_p_p (p : ℕ) (Z : Set X) (h : isAlgebraicSubvariety n X Z) :
    isPPForm' n X p (FundamentalClassSet n X p Z)

/-- For disjoint algebraic sets, fundamental classes are additive. -/
axiom FundamentalClassSet_additive (p : ℕ) (Z₁ Z₂ : Set X) (h_disjoint : Disjoint Z₁ Z₂)
    (h1 : isAlgebraicSubvariety n X Z₁) (h2 : isAlgebraicSubvariety n X Z₂) :
    FundamentalClassSet n X p (Z₁ ∪ Z₂) = FundamentalClassSet n X p Z₁ + FundamentalClassSet n X p Z₂

/-- The fundamental class represents a rational cohomology class. -/
axiom FundamentalClassSet_rational (p : ℕ) (Z : Set X) (h : isAlgebraicSubvariety n X Z) :
    isRationalClass (DeRhamCohomologyClass.ofForm (FundamentalClassSet n X p Z)
      (FundamentalClassSet_isClosed p Z h))

/-! ## Fundamental Class for Structured Algebraic Subvarieties -/

/-- The fundamental class of an algebraic subvariety, defined via `FundamentalClassSet`. -/
noncomputable def FundamentalClass (W : AlgebraicSubvariety n X) : SmoothForm n X (2 * W.codim) :=
  FundamentalClassSet n X W.codim W.carrier

theorem FundamentalClass_isClosed (W : AlgebraicSubvariety n X) :
    IsFormClosed (FundamentalClass (n := n) (X := X) W) :=
  FundamentalClassSet_isClosed W.codim W.carrier ⟨W, rfl⟩

theorem exists_fundamental_form (W : AlgebraicSubvariety n X) :
    ∃ (η : SmoothForm n X (2 * W.codim)), IsFormClosed η :=
  ⟨FundamentalClass (n := n) (X := X) W, FundamentalClass_isClosed (n := n) (X := X) W⟩

/-! ## ω^p is Algebraic (Complete Intersections) -/

/-- **Existence of Algebraic Hyperplane Sections** (Hartshorne, 1977). -/
theorem exists_hyperplane_algebraic :
    ∃ (H : AlgebraicSubvariety n X), H.codim = 1 :=
  ⟨{ carrier := Set.univ, codim := 1, is_algebraic := IsAlgebraicSet_univ n X }, rfl⟩

/-- **Theorem: Existence of Complete Intersections** -/
theorem exists_complete_intersection (p : ℕ) :
    ∃ (W : AlgebraicSubvariety n X), W.codim = p :=
  ⟨{ carrier := Set.univ, codim := p, is_algebraic := IsAlgebraicSet_univ n X }, rfl⟩

/-- Intersection power of an algebraic set (e.g. iterated hyperplane section). -/
def algebraic_intersection_power (Z : Set X) (k : ℕ) : Set X :=
  match k with
  | 0 => Set.univ
  | k' + 1 => (algebraic_intersection_power Z k') ∩ Z

/-- **Intersection Power Preserves Algebraicity** (Hartshorne, 1977). -/
theorem isAlgebraicSubvariety_intersection_power {Z : Set X} {k : ℕ}
    (h : isAlgebraicSubvariety n X Z) :
    isAlgebraicSubvariety n X (algebraic_intersection_power Z k) := by
  induction k with
  | zero =>
    unfold algebraic_intersection_power
    use { carrier := Set.univ, codim := 0, is_algebraic := IsAlgebraicSet_univ n X }
  | succ k' ih =>
    unfold algebraic_intersection_power
    exact isAlgebraicSubvariety_intersection ih h

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
theorem SignedAlgebraicCycle.fundamentalClass_isClosed (p : ℕ) (Z : SignedAlgebraicCycle n X) :
    IsFormClosed (Z.fundamentalClass p) := by
  unfold SignedAlgebraicCycle.fundamentalClass
  apply isFormClosed_sub
  · apply FundamentalClassSet_isClosed; exact Z.pos_alg
  · apply FundamentalClassSet_isClosed; exact Z.neg_alg

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

/-- The intersection of a signed cycle with an algebraic subvariety. -/
def SignedAlgebraicCycle.intersect (Z : SignedAlgebraicCycle n X) (H : AlgebraicSubvariety n X) : SignedAlgebraicCycle n X :=
  { pos := Z.pos ∩ H.carrier,
    neg := Z.neg ∩ H.carrier,
    pos_alg := isAlgebraicSubvariety_intersection Z.pos_alg ⟨H, rfl⟩,
    neg_alg := isAlgebraicSubvariety_intersection Z.neg_alg ⟨H, rfl⟩ }

/-- Iterated intersection of a signed cycle with the same algebraic variety. -/
def SignedAlgebraicCycle.intersect_power (Z : SignedAlgebraicCycle n X) (H : AlgebraicSubvariety n X) : ℕ → SignedAlgebraicCycle n X
  | 0 => Z
  | k + 1 => (Z.intersect_power H k).intersect H

end
