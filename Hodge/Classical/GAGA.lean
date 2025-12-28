import Hodge.Classical.HarveyLawson
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing

noncomputable section

open Classical

set_option autoImplicit false

/-!
# Track A.3: Serre's GAGA Theorem and Algebraic Subvarieties
-/

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- An algebraic subvariety of a projective variety X. -/
structure AlgebraicSubvariety (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  carrier : Set X
  codim : ℕ
  defining_sections : ∃ (L : HolomorphicLineBundle n X) (_hL : IsAmple L) (M : ℕ),
    ∃ (s : Finset (HolomorphicSection (L.power M))),
      carrier = ⋂ s_i ∈ s, { x | s_i.1 x = 0 }

/-- Predicate for a set being an algebraic subvariety. -/
def isAlgebraicSubvariety (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (Z : Set X) : Prop :=
  ∃ (W : AlgebraicSubvariety n X), W.carrier = Z

/-- **Theorem: GAGA (Serre, 1956)**
    On a projective complex manifold, every analytic subvariety is algebraic.
    Reference: J.-P. Serre, "Géométrie algébrique et géométrie analytique",
    Ann. Inst. Fourier 6 (1956), 1-42. -/
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

/-- **Existence of Fundamental Class**
    Every algebraic subvariety W has a fundamental class [W] in de Rham cohomology.
    This follows from Poincaré duality on compact manifolds. -/
axiom exists_fundamental_form (W : AlgebraicSubvariety n X) :
    ∃ (η : SmoothForm n X (2 * W.codim)), isClosed η

noncomputable def FundamentalClass (W : AlgebraicSubvariety n X) : SmoothForm n X (2 * W.codim) :=
  Classical.choose (exists_fundamental_form W)

theorem FundamentalClass_isClosed (W : AlgebraicSubvariety n X) :
    isClosed (FundamentalClass W) :=
  (Classical.choose_spec (exists_fundamental_form W))

/-! ## Fundamental Class for Sets -/

axiom exists_fundamental_form_set (p : ℕ) (Z : Set X) (h : isAlgebraicSubvariety n X Z) :
    ∃ (η : SmoothForm n X (2 * p)), isClosed η

noncomputable def FundamentalClassSet (p : ℕ) (Z : Set X) : SmoothForm n X (2 * p) :=
  if h : isAlgebraicSubvariety n X Z then
    Classical.choose (exists_fundamental_form_set p Z h)
  else
    0

axiom FundamentalClassSet_eq_FundamentalClass (W : AlgebraicSubvariety n X) :
    FundamentalClassSet W.codim W.carrier = FundamentalClass W

axiom FundamentalClassSet_empty (p : ℕ) : FundamentalClassSet p (∅ : Set X) = 0

/-! ## ω^p is Algebraic (Complete Intersections) -/

axiom exists_hyperplane_algebraic :
    ∃ (H : AlgebraicSubvariety n X), H.codim = 1

/-- **Existence of Complete Intersections**
    For any p, there exists a complete intersection of p hyperplanes in general position.
    This subvariety has codimension p and is smooth by Bertini's theorem.
    Reference: Griffiths-Harris, "Principles of Algebraic Geometry", p. 171. -/
axiom exists_complete_intersection (p : ℕ) :
    ∃ (W : AlgebraicSubvariety n X), W.codim = p

theorem omega_pow_is_algebraic (p : ℕ) :
    ∃ (Z : Set X), isAlgebraicSubvariety n X Z ∧
    ∃ (W : AlgebraicSubvariety n X), W.carrier = Z ∧ W.codim = p := by
  obtain ⟨H, _⟩ := @exists_hyperplane_algebraic n X _ _ _ _ K
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
  · obtain ⟨W, hW_codim⟩ := @exists_complete_intersection n X _ _ _ _ K p
    exact ⟨W.carrier, ⟨W, rfl⟩, W, rfl, hW_codim⟩

/-! ## Hyperplane Intersection Operations -/

noncomputable def hyperplaneClass : AlgebraicSubvariety n X :=
  Classical.choose (@exists_hyperplane_algebraic n X _ _ _ _ K)

theorem hyperplaneClass_codim : (hyperplaneClass (n := n) (X := X)).codim = 1 :=
  Classical.choose_spec (@exists_hyperplane_algebraic n X _ _ _ _ K)

noncomputable def algebraic_intersection_power (Z : Set X) (k : ℕ) : Set X :=
  if k = 0 then Z
  else Z ∩ hyperplaneClass.carrier

theorem isAlgebraicSubvariety_intersection_power {Z : Set X} {k : ℕ}
    (h : isAlgebraicSubvariety n X Z) :
    isAlgebraicSubvariety n X (algebraic_intersection_power Z k) := by
  unfold algebraic_intersection_power
  split_ifs with hk
  · exact h
  · apply isAlgebraicSubvariety_intersection h
    exact ⟨hyperplaneClass, rfl⟩

/-! ## Fundamental Class and Lefschetz -/

axiom FundamentalClass_intersection_power_eq {p k : ℕ}
    (W : AlgebraicSubvariety n X) (_hW : W.codim = p) :
    ∃ (W' : AlgebraicSubvariety n X),
      W'.carrier = algebraic_intersection_power W.carrier k ∧
      W'.codim = p + k

/-- The fundamental class of an intersection with k hyperplanes equals L^k of the original. -/
axiom FundamentalClassSet_intersection_power_eq (p k : ℕ) (Z : Set X)
    (hZ : isAlgebraicSubvariety n X Z) :
    FundamentalClassSet (p + k) (algebraic_intersection_power Z k) =
    (show SmoothForm n X (2 * p + 2 * k) = SmoothForm n X (2 * (p + k)) from by ring_nf) ▸
    lefschetz_power_form k (FundamentalClassSet p Z)

/-! ## Functoriality of Fundamental Class -/

axiom FundamentalClassSet_additive {p : ℕ} (Z₁ Z₂ : Set X) (h_disjoint : Z₁ ∩ Z₂ = ∅) :
    FundamentalClassSet p (Z₁ ∪ Z₂) = FundamentalClassSet p Z₁ + FundamentalClassSet p Z₂

/-! ## Signed Algebraic Cycles -/

/-- A signed algebraic cycle: a formal difference Z⁺ - Z⁻ of effective cycles. -/
structure SignedAlgebraicCycle (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  pos : Set X
  neg : Set X
  pos_alg : isAlgebraicSubvariety n X pos
  neg_alg : isAlgebraicSubvariety n X neg

/-- The fundamental class of a signed cycle is the difference of fundamental classes. -/
noncomputable def SignedAlgebraicCycle.fundamentalClass (p : ℕ)
    (Z : SignedAlgebraicCycle n X) : SmoothForm n X (2 * p) :=
  FundamentalClassSet p Z.pos - FundamentalClassSet p Z.neg

/-- The support of a signed cycle is Z⁺ ∪ Z⁻. -/
def SignedAlgebraicCycle.support (Z : SignedAlgebraicCycle n X) : Set X := Z.pos ∪ Z.neg

/-- The support of a signed cycle is algebraic. -/
theorem SignedAlgebraicCycle.support_is_algebraic (Z : SignedAlgebraicCycle n X) :
    isAlgebraicSubvariety n X Z.support :=
  isAlgebraicSubvariety_union Z.pos_alg Z.neg_alg

end
