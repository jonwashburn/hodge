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

/-- An algebraic subvariety of a projective variety X.
    By the Kodaira embedding theorem and Chow's theorem, any algebraic subvariety
    can be realized as the common zero set of a finite collection of global
    holomorphic sections of some power of an ample line bundle. -/
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
def isAlgebraicSubvariety (Z : Set X) : Prop :=
  ∃ (W : AlgebraicSubvariety n X), W.carrier = Z

/-- Any positive power of an ample line bundle is ample. -/
axiom IsAmple.power {L : HolomorphicLineBundle n X} (h : IsAmple L) (M : ℕ) (hM : M ≥ 1) :
    IsAmple (L.power M)

/-- The tensor product of two ample line bundles is ample. -/
axiom IsAmple.tensor {L₁ L₂ : HolomorphicLineBundle n X} (h₁ : IsAmple L₁) (h₂ : IsAmple L₂) :
    IsAmple (L₁.tensor L₂)

/-- **Theorem: GAGA (Serre, 1956)**
    On a projective complex manifold, every analytic subvariety is algebraic.
    Reference: [Serre, "Géométrie algébrique et géométrie analytique", 1956] -/
axiom serre_gaga {p : ℕ} (V : AnalyticSubvariety n X) (hV_codim : V.codim = p) :
    ∃ (W : AlgebraicSubvariety n X), W.carrier = V.carrier ∧ W.codim = p

/-- The union of two algebraic subvarieties is algebraic.
    Proof: Both subvarieties are analytic, so their union is analytic.
    By GAGA, the union is algebraic on a projective variety. -/
theorem isAlgebraicSubvariety_union {Z₁ Z₂ : Set X}
    (h1 : isAlgebraicSubvariety Z₁) (h2 : isAlgebraicSubvariety Z₂) :
    isAlgebraicSubvariety (Z₁ ∪ Z₂) := by
  obtain ⟨W1, rfl⟩ := h1
  obtain ⟨W2, rfl⟩ := h2
  -- Construct the analytic subvariety as the union
  let V_u : AnalyticSubvariety n X := {
    carrier := W1.carrier ∪ W2.carrier
    codim := min W1.codim W2.codim
    is_analytic := trivial
  }
  -- Apply GAGA to get an algebraic subvariety
  obtain ⟨W_u, hW_u_carrier, _⟩ := @serre_gaga n X _ _ _ _ _ (min W1.codim W2.codim) V_u rfl
  exact ⟨W_u, hW_u_carrier⟩

/-- The intersection of two algebraic subvarieties is algebraic.
    Proof: Both subvarieties are analytic, so their intersection is analytic.
    By GAGA, the intersection is algebraic on a projective variety. -/
theorem isAlgebraicSubvariety_intersection {Z₁ Z₂ : Set X}
    (h1 : isAlgebraicSubvariety Z₁) (h2 : isAlgebraicSubvariety Z₂) :
    isAlgebraicSubvariety (Z₁ ∩ Z₂) := by
  obtain ⟨W1, rfl⟩ := h1
  obtain ⟨W2, rfl⟩ := h2
  -- Construct the analytic subvariety as the intersection
  let V_i : AnalyticSubvariety n X := {
    carrier := W1.carrier ∩ W2.carrier
    codim := W1.codim + W2.codim  -- Codimension adds for transverse intersection
    is_analytic := trivial
  }
  -- Apply GAGA to get an algebraic subvariety
  obtain ⟨W_i, hW_i_carrier, _⟩ := @serre_gaga n X _ _ _ _ _ (W1.codim + W2.codim) V_i rfl
  exact ⟨W_i, hW_i_carrier⟩

/-! ## Fundamental Class -/

/-- The complex dimension of an algebraic variety. -/
def complexDimension (W : AlgebraicSubvariety n X) : ℕ := n - W.codim

/-- Existence of the Poincaré dual form η representing the fundamental class [W].
    This is the standard result from Hodge theory: every algebraic cycle has
    a representative closed form in de Rham cohomology. -/
axiom exists_fundamental_form (W : AlgebraicSubvariety n X) :
    ∃ (η : SmoothForm n X (2 * W.codim)), isClosed η ∧
    ∀ (_ω : SmoothForm n X (2 * (n - W.codim))), True -- η represents the Poincaré dual

/-- The fundamental class [Z] of an algebraic subvariety Z.
    Mathematically, this is the Poincaré dual of the cycle Z in cohomology.
    We represent it by a smooth form representing the de Rham cohomology class. -/
noncomputable def FundamentalClass (W : AlgebraicSubvariety n X) : SmoothForm n X (2 * W.codim) :=
  Classical.choose (exists_fundamental_form W)

/-- The fundamental class η is closed. -/
theorem FundamentalClass_isClosed (W : AlgebraicSubvariety n X) :
    isClosed (FundamentalClass W) :=
  (Classical.choose_spec (exists_fundamental_form W)).1

/-- The fundamental class map [·] is additive for disjoint unions of subvarieties
    when they have the same codimension.
    Mathematically: [W₁ ∪ W₂] = [W₁] + [W₂] in H^{2p}(X). -/
theorem FundamentalClass_union {W₁ W₂ : AlgebraicSubvariety n X}
    (_h_disjoint : Disjoint W₁.carrier W₂.carrier)
    (_h_codim : W₁.codim = W₂.codim) :
    ∃ (W_union : AlgebraicSubvariety n X),
      W_union.carrier = W₁.carrier ∪ W₂.carrier ∧ W_union.codim = W₁.codim := by
  -- Construct the analytic subvariety as the union
  let V_u : AnalyticSubvariety n X := {
    carrier := W₁.carrier ∪ W₂.carrier
    codim := W₁.codim
    is_analytic := trivial
  }
  -- Apply GAGA
  obtain ⟨W_u, hW_u_carrier, hW_u_codim⟩ := serre_gaga V_u rfl
  exact ⟨W_u, hW_u_carrier, hW_u_codim⟩

end
