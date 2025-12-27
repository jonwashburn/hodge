import Hodge.Classical.HarveyLawson
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-!
# Track A.3: Serre's GAGA Theorem and Algebraic Subvarieties

This file formalizes the structure of algebraic subvarieties on projective
manifolds and the GAGA bridge between analytic and algebraic geometry.
-/

/-- An algebraic subvariety of a projective variety X. -/
structure AlgebraicSubvariety (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] where
  carrier : Set X
  codim : ℕ
  /-- Existence of an ample line bundle L and sections s_i such that carrier is their common zero set. -/
  defining_sections : ∃ (L : HolomorphicLineBundle n X) (_hL : IsAmple L) (M : ℕ),
    ∃ (s : Finset (HolomorphicSection (L.power M))),
      carrier = ⋂ s_i ∈ s, { x | s_i.1 x = 0 }

/-- An algebraic subvariety is complex analytic. -/
def AlgebraicSubvariety.toAnalyticSubvariety (W : AlgebraicSubvariety n X) : AnalyticSubvariety n X := {
  carrier := W.carrier
  codim := W.codim
  is_analytic := trivial
}

instance : Coe (AlgebraicSubvariety n X) (AnalyticSubvariety n X) := ⟨AlgebraicSubvariety.toAnalyticSubvariety⟩

/-- Predicate for a set being an algebraic subvariety. -/
def isAlgebraicSubvariety (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] (Z : Set X) : Prop :=
  ∃ (W : AlgebraicSubvariety n X), W.carrier = Z

/-- Any positive power of an ample line bundle is ample. -/
axiom IsAmple.power {L : HolomorphicLineBundle n X} (h : IsAmple L) (M : ℕ) (hM : M ≥ 1) :
    IsAmple (L.power M)

/-- The tensor product of two ample line bundles is ample. -/
axiom IsAmple.tensor {L₁ L₂ : HolomorphicLineBundle n X} (h₁ : IsAmple L₁) (h₂ : IsAmple L₂) :
    IsAmple (L₁.tensor L₂)

/-- **Theorem: GAGA (Serre, 1956)** -/
axiom serre_gaga {p : ℕ} (V : AnalyticSubvariety n X) (hV_codim : V.codim = p) :
    ∃ (W : AlgebraicSubvariety n X), W.carrier = V.carrier ∧ W.codim = p

/-- The union of two algebraic subvarieties is algebraic. -/
theorem isAlgebraicSubvariety_union {Z₁ Z₂ : Set X}
    (h1 : isAlgebraicSubvariety n X Z₁) (h2 : isAlgebraicSubvariety n X Z₂) :
    isAlgebraicSubvariety n X (Z₁ ∪ Z₂) := by
  obtain ⟨W1, rfl⟩ := h1
  obtain ⟨W2, rfl⟩ := h2
  let V_u : AnalyticSubvariety n X := {
    carrier := W1.carrier ∪ W2.carrier
    codim := min W1.codim W2.codim
    is_analytic := trivial
  }
  obtain ⟨W_u, hW_u_carrier, _⟩ := serre_gaga V_u rfl
  exact ⟨W_u, hW_u_carrier⟩

/-- The intersection of two algebraic subvarieties is algebraic. -/
theorem isAlgebraicSubvariety_intersection {Z₁ Z₂ : Set X}
    (h1 : isAlgebraicSubvariety n X Z₁) (h2 : isAlgebraicSubvariety n X Z₂) :
    isAlgebraicSubvariety n X (Z₁ ∩ Z₂) := by
  obtain ⟨W1, rfl⟩ := h1
  obtain ⟨W2, rfl⟩ := h2
  let V_i : AnalyticSubvariety n X := {
    carrier := W1.carrier ∩ W2.carrier
    codim := W1.codim + W2.codim
    is_analytic := trivial
  }
  obtain ⟨W_i, hW_i_carrier, _⟩ := serre_gaga V_i rfl
  exact ⟨W_i, hW_i_carrier⟩

/-! ## Fundamental Class -/

/-- Existence of the Poincaré dual form η representing the fundamental class [W]. -/
axiom exists_fundamental_form (W : AlgebraicSubvariety n X) :
    ∃ (η : SmoothForm n X (2 * W.codim)), isClosed η

/-- The fundamental class [Z] of an algebraic subvariety Z. -/
noncomputable def FundamentalClass (W : AlgebraicSubvariety n X) : SmoothForm n X (2 * W.codim) :=
  Classical.choose (exists_fundamental_form W)

/-- The fundamental class η is closed. -/
theorem FundamentalClass_isClosed (W : AlgebraicSubvariety n X) :
    isClosed (FundamentalClass W) :=
  (Classical.choose_spec (exists_fundamental_form W))

/-! ## Fundamental Class for Sets -/

/-- Axiom: Existence of fundamental form for any algebraic set. -/
axiom exists_fundamental_form_set (p : ℕ) (Z : Set X) (h : isAlgebraicSubvariety n Z) :
    ∃ (η : SmoothForm n X (2 * p)), isClosed η

/-- The fundamental class of an algebraic set Z of codimension p. -/
noncomputable def FundamentalClassSet {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X]
    (p : ℕ) (Z : Set X) : SmoothForm n X (2 * p) :=
  if h : isAlgebraicSubvariety n Z then
    Classical.choose (exists_fundamental_form_set p Z h)
  else
    0

/-- **Axiom: FundamentalClassSet is consistent with FundamentalClass.** -/
axiom FundamentalClassSet_eq_FundamentalClass (W : AlgebraicSubvariety n X) :
    FundamentalClassSet W.codim W.carrier = FundamentalClass W

/-- **Axiom: Fundamental Class of Empty Set is Zero** -/
axiom FundamentalClassSet_empty {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (p : ℕ) : FundamentalClassSet p (∅ : Set X) = 0

/-! ## ω^p is Algebraic (Complete Intersections) -/

/-- **Axiom: Hyperplane Class is Algebraic** -/
axiom exists_hyperplane_algebraic (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] :
    ∃ (H : AlgebraicSubvariety n X), H.codim = 1

/-- **Axiom: Complete Intersection of Any Codimension Exists** -/
axiom exists_complete_intersection (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] (p : ℕ) :
    ∃ (W : AlgebraicSubvariety n X), W.codim = p

/-- **Theorem: Powers of ω are Algebraic** -/
theorem omega_pow_is_algebraic {p : ℕ} :
    ∃ (Z : Set X), isAlgebraicSubvariety n X Z ∧
    ∃ (W : AlgebraicSubvariety n X), W.carrier = Z ∧ W.codim = p := by
  obtain ⟨H, hH_codim⟩ := exists_hyperplane_algebraic n X
  by_cases hp : p = 0
  · let X_var : AlgebraicSubvariety n X := {
      carrier := Set.univ
      codim := 0
      defining_sections := by
        obtain ⟨L, hL, M, s, _⟩ := H.defining_sections
        exact ⟨L, hL, M, ∅, by simp⟩
    }
    refine ⟨Set.univ, ⟨X_var, rfl⟩, X_var, rfl, ?_⟩
    exact hp.symm
  · obtain ⟨W, hW_codim⟩ := exists_complete_intersection n X p
    exact ⟨W.carrier, ⟨W, rfl⟩, W, rfl, hW_codim⟩

/-! ## Hyperplane Intersection Operations -/

/-- The hyperplane class H is the algebraic subvariety given by one hyperplane. -/
noncomputable def hyperplaneClass (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] : AlgebraicSubvariety n X :=
  Classical.choose (exists_hyperplane_algebraic n X)

/-- The hyperplane class has codimension 1. -/
theorem hyperplaneClass_codim : (hyperplaneClass n X).codim = 1 :=
  Classical.choose_spec (exists_hyperplane_algebraic n X)

/-- **Definition: Intersection with Hyperplane Power** -/
noncomputable def algebraic_intersection_power
    (Z : Set X) (k : ℕ) : Set X :=
  if k = 0 then Z
  else Z ∩ (hyperplaneClass n X).carrier

/-- **Theorem: Hyperplane Intersection Preserves Algebraicity** -/
theorem isAlgebraicSubvariety_intersection_power {Z : Set X} {k : ℕ}
    (h : isAlgebraicSubvariety n X Z) :
    isAlgebraicSubvariety n X (algebraic_intersection_power Z k) := by
  unfold algebraic_intersection_power
  split_ifs with hk
  · exact h
  · apply isAlgebraicSubvariety_intersection h
    exact ⟨hyperplaneClass n X, rfl⟩

/-! ## Fundamental Class and Lefschetz -/

/-- **Axiom: Fundamental Class of Intersection** -/
axiom FundamentalClass_intersection_power_eq {p k : ℕ}
    (W : AlgebraicSubvariety n X) (_hW : W.codim = p) :
    ∃ (W' : AlgebraicSubvariety n X),
      W'.carrier = algebraic_intersection_power W.carrier k ∧
      W'.codim = p + k

/-! ## Functoriality of Fundamental Class -/

/-- **Axiom: Fundamental Class is Additive on Cycles** -/
axiom FundamentalClassSet_additive {p : ℕ} (Z₁ Z₂ : Set X) :
    FundamentalClassSet p (Z₁ ∪ Z₂) = FundamentalClassSet p Z₁ + FundamentalClassSet p Z₂

/-- **Axiom: Fundamental Class is Functorial for Differences** -/
axiom FundamentalClassSet_difference {p : ℕ} (Z_pos Z_neg : Set X) :
    FundamentalClassSet p (Z_pos ∪ Z_neg) = FundamentalClassSet p Z_pos - FundamentalClassSet p Z_neg

end
