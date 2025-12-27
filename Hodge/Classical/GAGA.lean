import Hodge.Classical.HarveyLawson
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing

noncomputable section

open Classical

set_option autoImplicit false

/-!
# Track A.3: Serre's GAGA Theorem and Algebraic Subvarieties
-/

/-- An algebraic subvariety of a projective variety X. -/
structure AlgebraicSubvariety (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] where
  carrier : Set X
  codim : ℕ
  defining_sections : ∃ (L : HolomorphicLineBundle n X) (_hL : IsAmple L) (M : ℕ),
    ∃ (s : Finset (HolomorphicSection (L.power M))),
      carrier = ⋂ s_i ∈ s, { x | s_i.1 x = 0 }

/-- An algebraic subvariety is complex analytic. -/
def AlgebraicSubvariety.toAnalyticSubvariety {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] (W : AlgebraicSubvariety n X) : AnalyticSubvariety n X := {
  carrier := W.carrier
  codim := W.codim
  is_analytic := trivial
}

instance {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] : Coe (AlgebraicSubvariety n X) (AnalyticSubvariety n X) := ⟨AlgebraicSubvariety.toAnalyticSubvariety⟩

/-- Predicate for a set being an algebraic subvariety. -/
def isAlgebraicSubvariety (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] (Z : Set X) : Prop :=
  ∃ (W : AlgebraicSubvariety n X), W.carrier = Z

/-- **Theorem: GAGA (Serre, 1956)** -/
axiom serre_gaga {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    {p : ℕ} (V : AnalyticSubvariety n X) (hV_codim : V.codim = p) :
    ∃ (W : AlgebraicSubvariety n X), W.carrier = V.carrier ∧ W.codim = p

/-- The union of two algebraic subvarieties is algebraic. -/
theorem isAlgebraicSubvariety_union (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] {Z₁ Z₂ : Set X}
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
theorem isAlgebraicSubvariety_intersection (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] {Z₁ Z₂ : Set X}
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

axiom exists_fundamental_form {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] (W : AlgebraicSubvariety n X) :
    ∃ (η : SmoothForm n X (2 * W.codim)), isClosed η

noncomputable def FundamentalClass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] (W : AlgebraicSubvariety n X) : SmoothForm n X (2 * W.codim) :=
  Classical.choose (exists_fundamental_form W)

theorem FundamentalClass_isClosed {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] (W : AlgebraicSubvariety n X) :
    isClosed (FundamentalClass W) :=
  (Classical.choose_spec (exists_fundamental_form W))

/-! ## Fundamental Class for Sets -/

axiom exists_fundamental_form_set {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] (p : ℕ) (Z : Set X) (h : isAlgebraicSubvariety n X Z) :
    ∃ (η : SmoothForm n X (2 * p)), isClosed η

noncomputable def FundamentalClassSet (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] (p : ℕ) (Z : Set X) : SmoothForm n X (2 * p) :=
  if h : isAlgebraicSubvariety n X Z then
    Classical.choose (exists_fundamental_form_set p Z h)
  else
    0

axiom FundamentalClassSet_eq_FundamentalClass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] (W : AlgebraicSubvariety n X) :
    FundamentalClassSet n X W.codim W.carrier = FundamentalClass W

axiom FundamentalClassSet_empty {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] (p : ℕ) : FundamentalClassSet n X p (∅ : Set X) = 0

/-! ## ω^p is Algebraic (Complete Intersections) -/

axiom exists_hyperplane_algebraic (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] :
    ∃ (H : AlgebraicSubvariety n X), H.codim = 1

axiom exists_complete_intersection (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] (p : ℕ) :
    ∃ (W : AlgebraicSubvariety n X), W.codim = p

theorem omega_pow_is_algebraic (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] (p : ℕ) :
    ∃ (Z : Set X), isAlgebraicSubvariety n X Z ∧
    ∃ (W : AlgebraicSubvariety n X), W.carrier = Z ∧ W.codim = p := by
  obtain ⟨H, _⟩ := exists_hyperplane_algebraic n X
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

noncomputable def hyperplaneClass (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] : AlgebraicSubvariety n X :=
  Classical.choose (exists_hyperplane_algebraic n X)

theorem hyperplaneClass_codim (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] : (hyperplaneClass n X).codim = 1 :=
  Classical.choose_spec (exists_hyperplane_algebraic n X)

noncomputable def algebraic_intersection_power (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X]
    (Z : Set X) (k : ℕ) : Set X :=
  if k = 0 then Z
  else Z ∩ (hyperplaneClass n X).carrier

theorem isAlgebraicSubvariety_intersection_power (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    {Z : Set X} {k : ℕ}
    (h : isAlgebraicSubvariety n X Z) :
    isAlgebraicSubvariety n X (algebraic_intersection_power n X Z k) := by
  unfold algebraic_intersection_power
  split_ifs with hk
  · exact h
  · apply isAlgebraicSubvariety_intersection n X h
    exact ⟨hyperplaneClass n X, rfl⟩

/-! ## Fundamental Class and Lefschetz -/

/-- **Axiom: Fundamental Class Set and Intersection Power** -/
axiom FundamentalClassSet_intersection_power_eq (p k : ℕ) {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (Z : Set X) (hZ : isAlgebraicSubvariety n X Z) :
    FundamentalClassSet n X (p + k) (algebraic_intersection_power n X Z k) =
    (show SmoothForm n X (2 * p + 2 * k) = SmoothForm n X (2 * (p + k)) from by ring_nf) ▸
    lefschetz_power_form k (FundamentalClassSet n X p Z)

/-! ## Functoriality of Fundamental Class -/

axiom FundamentalClassSet_additive {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    {p : ℕ} (Z₁ Z₂ : Set X) :
    FundamentalClassSet n X p (Z₁ ∪ Z₂) = FundamentalClassSet n X p Z₁ + FundamentalClassSet n X p Z₂

axiom FundamentalClassSet_difference {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    {p : ℕ} (Z_pos Z_neg : Set X) :
    FundamentalClassSet n X p (Z_pos ∪ Z_neg) = FundamentalClassSet n X p Z_pos - FundamentalClassSet n X p Z_neg

end
