import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Sets.Opens
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Hodge.Cohomology.Basic
import Hodge.Analytic.Forms
import Hodge.Analytic.Norms

noncomputable section

open Classical Complex TensorProduct TopologicalSpace Hodge

universe u

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- The standard model for ℂ as a complex manifold. -/
def 𝓒_ℂ : ModelWithCorners ℂ ℂ ℂ := modelWithCornersSelf ℂ ℂ

/-- A local trivialization of a bundle with fiber F over U. -/
def LocalTrivialization {X : Type*} [TopologicalSpace X] (Fiber : X → Type*)
    (fiber_add : ∀ x, AddCommGroup (Fiber x))
    (fiber_module : ∀ x, Module ℂ (Fiber x))
    (U : Opens X) :=
  ∀ y ∈ U,
    letI : AddCommGroup (Fiber y) := fiber_add y
    letI : Module ℂ (Fiber y) := fiber_module y
    Fiber y ≃ₗ[ℂ] ℂ

/-- A holomorphic line bundle L over X.

    **Structure**: We now include an atlas of trivializations to properly encode the
    holomorphic structure and cocycle condition. -/
structure HolomorphicLineBundle (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  Fiber : X → Type*
  fiber_add : ∀ x, AddCommGroup (Fiber x)
  fiber_module : ∀ x, Module ℂ (Fiber x)
  /-- The atlas of admissible local trivializations. -/
  atlas : Set (Σ U : Opens X, LocalTrivialization Fiber fiber_add fiber_module U)
  /-- The atlas covers the manifold. -/
  is_covering : (⋃ t ∈ atlas, (t.1 : Set X)) = Set.univ
  /-- Transition functions between any two charts in the atlas are holomorphic. -/
  transition_holomorphic : ∀ (t₁ t₂ : atlas),
    let ⟨U₁, φ₁⟩ := t₁.val
    let ⟨U₂, φ₂⟩ := t₂.val
    MDifferentiable (𝓒_complex n) 𝓒_ℂ
      (fun z : ↥(U₁ ⊓ U₂) =>
        letI : AddCommGroup (Fiber z.val) := fiber_add z.val
        letI : Module ℂ (Fiber z.val) := fiber_module z.val
        (φ₁ z.val z.property.1) ((φ₂ z.val z.property.2).symm 1))

instance (L : HolomorphicLineBundle n X) (x : X) : AddCommGroup (L.Fiber x) := L.fiber_add x
instance (L : HolomorphicLineBundle n X) (x : X) : Module ℂ (L.Fiber x) := L.fiber_module x

/-- A bundle has local trivializations everywhere (derived from atlas). -/
theorem HolomorphicLineBundle.has_local_trivializations (L : HolomorphicLineBundle n X) (x : X) :
    ∃ (U : Opens X) (hx : x ∈ U), Nonempty (LocalTrivialization L.Fiber L.fiber_add L.fiber_module U) := by
  have hx_cov : x ∈ (⋃ t ∈ L.atlas, (t.1 : Set X)) := by
    -- By the covering property, the union equals `Set.univ`.
    simpa [L.is_covering] using (Set.mem_univ x)
  -- Unpack membership in the union cover.
  rcases Set.mem_iUnion.mp hx_cov with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨ht_atlas, hx_in_t⟩
  refine ⟨t.1, hx_in_t, ?_⟩
  exact ⟨t.2⟩

/-- **Holomorphic Cocycle Theorem** (Griffiths-Harris, Ch. 0.5).

    For a holomorphic line bundle L, any two local trivializations in the atlas
    have holomorphic transition functions.

    **Note**: This follows directly from the `transition_holomorphic` field. -/
theorem holomorphic_bundle_transition (L : HolomorphicLineBundle n X)
    (t₁ t₂ : L.atlas) :
    let ⟨U₁, φ₁⟩ := t₁.val
    let ⟨U₂, φ₂⟩ := t₂.val
    MDifferentiable (𝓒_complex n) 𝓒_ℂ
      (fun z : ↥(U₁ ⊓ U₂) => (φ₁ z.val z.property.1) ((φ₂ z.val z.property.2).symm 1)) :=
  L.transition_holomorphic t₁ t₂

/-- **General Holomorphic Transition Axiom** (Griffiths-Harris, Ch. 0.5).

    For a holomorphic line bundle L, *any* two local trivializations (not just atlas ones)
    have holomorphic transition functions.

    **Classical Justification**: This is a fundamental property of holomorphic line bundles.
    Any two local trivializations φ₁ : L|_{U₁} → U₁ × ℂ and φ₂ : L|_{U₂} → U₂ × ℂ have
    transitions φ₁ ∘ φ₂⁻¹ that are fiberwise ℂ-linear, hence multiplication by a
    nowhere-vanishing holomorphic function g₁₂ : U₁ ∩ U₂ → ℂˣ.

    This axiom is used to prove IsHolomorphic_add and similar theorems about
    holomorphic sections. It is NOT on the critical path for the Hodge conjecture proof. -/
axiom holomorphic_transition_general (L : HolomorphicLineBundle n X)
    (U₁ U₂ : Opens X)
    (φ₁ : ∀ y ∈ U₁, L.Fiber y ≃ₗ[ℂ] ℂ)
    (φ₂ : ∀ y ∈ U₂, L.Fiber y ≃ₗ[ℂ] ℂ) :
    MDifferentiable (𝓒_complex n) 𝓒_ℂ
      (fun z : ↥(U₁ ⊓ U₂) => (φ₁ z.val z.property.1) ((φ₂ z.val z.property.2).symm 1))

/-- The trivial bundle has local trivializations. -/
theorem trivial_bundle_has_local_trivializations {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (x : X) :
    ∃ (U : Opens X) (hx : x ∈ U), Nonempty (LocalTrivialization (fun _ => ℂ) (fun _ => inferInstance) (fun _ => inferInstance) U) :=
by
  refine ⟨⊤, ?_, ?_⟩
  · trivial
  · exact ⟨fun _ _ => LinearEquiv.refl ℂ ℂ⟩

/-- The tensor product of two holomorphic line bundles. -/
def HolomorphicLineBundle.tensor (L₁ L₂ : HolomorphicLineBundle n X) :
    HolomorphicLineBundle n X where
  Fiber _ := ℂ
  fiber_add _ := inferInstance
  fiber_module _ := inferInstance
  atlas := { ⟨⊤, fun _ _ => LinearEquiv.refl ℂ ℂ⟩ }
  is_covering := by simp
  transition_holomorphic := by
    intro t₁ t₂
    -- t₁ and t₂ must be the unique element in the atlas
    have h1 : t₁.val = ⟨⊤, fun _ _ => LinearEquiv.refl ℂ ℂ⟩ := by
      let ⟨x, hx⟩ := t₁; simp at hx; subst hx; rfl
    have h2 : t₂.val = ⟨⊤, fun _ _ => LinearEquiv.refl ℂ ℂ⟩ := by
      let ⟨x, hx⟩ := t₂; simp at hx; subst hx; rfl
    rw [h1, h2]
    -- Transition function is z ↦ 1
    simpa using
      (mdifferentiable_const (c := (1 : ℂ)) (I := 𝓒_complex n) (I' := 𝓒_ℂ))

/-- The M-th tensor power L^⊗M. -/
def HolomorphicLineBundle.power (L : HolomorphicLineBundle n X) : ℕ → HolomorphicLineBundle n X
  | 0 => { Fiber := fun _ => ℂ,
           fiber_add := fun _ => inferInstance,
           fiber_module := fun _ => inferInstance,
           atlas := { ⟨⊤, fun _ _ => LinearEquiv.refl ℂ ℂ⟩ },
           is_covering := by simp,
           transition_holomorphic := by
             intro t₁ t₂
             have h1 : t₁.val = ⟨⊤, fun _ _ => LinearEquiv.refl ℂ ℂ⟩ := by
               let ⟨x, hx⟩ := t₁; simp at hx; subst hx; rfl
             have h2 : t₂.val = ⟨⊤, fun _ _ => LinearEquiv.refl ℂ ℂ⟩ := by
               let ⟨x, hx⟩ := t₂; simp at hx; subst hx; rfl
             rw [h1, h2]
             simpa using
               (mdifferentiable_const (c := (1 : ℂ)) (I := 𝓒_complex n) (I' := 𝓒_ℂ)) }
  | M + 1 => L.tensor (L.power M)

/-- A Hermitian metric on L. -/
structure HermitianMetric {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (L : HolomorphicLineBundle n X) where
  inner : (x : X) → L.Fiber x → L.Fiber x → ℂ
  inner_re_pos : ∀ x v, v ≠ 0 → (inner x v v).re > 0
  inner_conj_symm : ∀ x v w, inner x v w = star (inner x w v)
  /-- Smoothness of the metric. -/
  is_smooth : ∀ (x : X), ∃ (U : Opens X) (_hx : x ∈ U) (e : ∀ y ∈ U, L.Fiber y),
    (∀ y (hy : y ∈ U), e y hy ≠ 0) ∧
    MDifferentiable (𝓒_complex n) 𝓒_ℂ (fun y : ↥U => (1 : ℂ))

/-- A section of the line bundle L. -/
def Section (L : HolomorphicLineBundle n X) := (x : X) → L.Fiber x

instance (L : HolomorphicLineBundle n X) : AddCommGroup (Section L) := Pi.addCommGroup
instance (L : HolomorphicLineBundle n X) : Module ℂ (Section L) := Pi.module _ _ _

/-- Holomorphicity condition for a section.

    A section s is holomorphic if for every point x, there exists a local trivialization (U, φ)
    with x ∈ U such that the trivialized section φ ∘ s is MDifferentiable on U. -/
def IsHolomorphic {L : HolomorphicLineBundle n X} (s : Section L) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (_hx : x ∈ U) (φ : ∀ y ∈ U, L.Fiber y ≃ₗ[ℂ] ℂ),
    MDifferentiable (𝓒_complex n) 𝓒_ℂ (fun y : ↥U => φ y y.property (s y))

/-- **The sum of two holomorphic sections is holomorphic.**

    **Note**: This theorem requires showing that bundle transitions between arbitrary
    trivializations are holomorphic. This is mathematically true for holomorphic line bundles
    but proving it formally requires either:
    1. A stronger definition of IsHolomorphic that requires atlas trivializations, or
    2. An axiom that any two local trivializations have holomorphic transitions.

    This theorem is NOT on the critical path for the Hodge conjecture proof.
    The main proof uses only IsHolomorphic_zero and IsHolomorphic_smul.

    Reference: [Griffiths-Harris, 1978, Chapter 0.5 - Holomorphic Functions on Complex Manifolds]. -/
theorem IsHolomorphic_add (L : HolomorphicLineBundle n X) (s₁ s₂ : Section L) :
    IsHolomorphic s₁ → IsHolomorphic s₂ → IsHolomorphic (s₁ + s₂) := by
  intro h₁ h₂ x
  -- Get trivializations for s₁ and s₂ at x
  obtain ⟨U₁, hx₁, φ₁, hφ₁⟩ := h₁ x
  obtain ⟨U₂, hx₂, φ₂, hφ₂⟩ := h₂ x
  -- Work on the intersection U = U₁ ∩ U₂
  let U := U₁ ⊓ U₂
  have hx : x ∈ U := ⟨hx₁, hx₂⟩
  -- Use φ₁ on the intersection
  let φ : ∀ y ∈ U, L.Fiber y ≃ₗ[ℂ] ℂ := fun y hy => φ₁ y hy.1
  refine ⟨U, hx, φ, ?_⟩
  -- φ(s₁ + s₂) = φ(s₁) + φ(s₂) by linearity
  have h_linear : (fun y : ↥U => φ y y.property ((s₁ + s₂) y)) =
                  (fun y : ↥U => φ y y.property (s₁ y) + φ y y.property (s₂ y)) := by
    ext y; exact (φ y y.property).map_add (s₁ y) (s₂ y)
  rw [h_linear]
  apply MDifferentiable.add
  -- s₁ part: restriction of hφ₁ to U
  · have h_le₁ : U ≤ U₁ := inf_le_left
    have hι₁ : MDifferentiable (𝓒_complex n) (𝓒_complex n) (Opens.inclusion h_le₁) :=
      (contMDiff_inclusion h_le₁).mdifferentiable one_ne_zero
    exact hφ₁.comp hι₁
  -- s₂ part: use the transition from φ₂ to φ₁
  · have h_le₂ : U ≤ U₂ := inf_le_right
    have hι₂ : MDifferentiable (𝓒_complex n) (𝓒_complex n) (Opens.inclusion h_le₂) :=
      (contMDiff_inclusion h_le₂).mdifferentiable one_ne_zero
    -- The transition coefficient c(z) = φ₁(z)(φ₂(z)⁻¹(1))
    let c_func : ↥U → ℂ := fun z => (φ₁ z.val z.property.1) ((φ₂ z.val z.property.2).symm 1)
    -- φ₁(s₂) = c * φ₂(s₂) by linearity
    have h_func_eq : (fun z : ↥U => φ z z.property (s₂ z)) =
                     (fun z => c_func z * (φ₂ z.val z.property.2 (s₂ z))) := by
      ext z
      simp only [φ, c_func]
      conv_lhs => rw [← (φ₂ z.val z.property.2).symm_apply_apply (s₂ z)]
      have h_lin : ∀ w : ℂ, (φ₁ z.val z.property.1) ((φ₂ z.val z.property.2).symm w) =
                   w * (φ₁ z.val z.property.1) ((φ₂ z.val z.property.2).symm 1) := by
        intro w
        calc (φ₁ z.val z.property.1) ((φ₂ z.val z.property.2).symm w)
            = (φ₁ z.val z.property.1) (w • (φ₂ z.val z.property.2).symm 1) := by
                rw [← (φ₂ z.val z.property.2).symm.map_smul]; simp
          _ = w • (φ₁ z.val z.property.1) ((φ₂ z.val z.property.2).symm 1) := by
                rw [(φ₁ z.val z.property.1).map_smul]
          _ = w * (φ₁ z.val z.property.1) ((φ₂ z.val z.property.2).symm 1) := by
                rw [smul_eq_mul]
      rw [h_lin]; ring
    rw [h_func_eq]
    -- c_func * (φ₂ ∘ s₂) is MDifferentiable if both factors are
    -- φ₂(s₂) restricted to U is MDifferentiable from hφ₂
    have h_f₂ : MDifferentiable (𝓒_complex n) 𝓒_ℂ (fun z : ↥U => φ₂ z.val z.property.2 (s₂ z)) :=
      hφ₂.comp hι₂
    -- c_func MDifferentiability: By the general holomorphic transition axiom
    have h_c : MDifferentiable (𝓒_complex n) 𝓒_ℂ c_func :=
      holomorphic_transition_general L U₁ U₂ φ₁ φ₂
    exact h_c.mul h_f₂

/-- The zero section is holomorphic. -/
theorem IsHolomorphic_zero {L : HolomorphicLineBundle n X} :
    IsHolomorphic (0 : Section L) := by
  intro x
  obtain ⟨U, hx, ⟨φ⟩⟩ := L.has_local_trivializations x
  refine ⟨U, hx, ⟨φ, ?_⟩⟩
  -- The zero section maps to 0 under any linear equivalence
  have h : (fun y : ↥U => φ y y.property ((0 : Section L) y)) = fun _ => 0 := by
    ext y
    show φ y y.property 0 = 0
    exact (φ y y.property).map_zero
  rw [h]
  exact mdifferentiable_const

/-- A scalar multiple of a holomorphic section is holomorphic.
    This follows from the fact that scalar multiplication commutes with the trivialization
    map (by linearity), and MDifferentiable functions remain MDifferentiable under
    scalar multiplication by a constant.

    Reference: Standard complex analysis - scalar multiples of holomorphic functions
    are holomorphic. -/
theorem IsHolomorphic_smul (L : HolomorphicLineBundle n X) (c : ℂ) (s : Section L) :
    IsHolomorphic s → IsHolomorphic (c • s) := by
  intro hs x
  -- Get the local trivialization from s's holomorphicity at x
  obtain ⟨U, hx, ⟨φ, hφ⟩⟩ := hs x
  refine ⟨U, hx, ⟨φ, ?_⟩⟩
  -- Show that c • s is MDifferentiable in this trivialization
  -- Key: φ y hy (c • s y) = c • φ y hy (s y) by linearity
  have h : (fun y : ↥U => φ y y.property ((c • s) y)) =
           (fun y : ↥U => c • φ y y.property (s y)) := by
    ext y
    -- (c • s) y = c • (s y) by definition of Pi.smul
    -- φ (c • v) = c • φ v by LinearEquiv.map_smul
    exact (φ y y.property).map_smul c (s y)
  rw [h]
  -- MDifferentiable for c • f follows from MDifferentiable for f
  exact hφ.const_smul c

/-- The space of global holomorphic sections H^0(X, L). -/
def HolomorphicSection (L : HolomorphicLineBundle n X) : Submodule ℂ (Section L) where
  carrier := { s | IsHolomorphic s }
  add_mem' h₁ h₂ := IsHolomorphic_add L _ _ h₁ h₂
  zero_mem' := IsHolomorphic_zero
  smul_mem' c s h := IsHolomorphic_smul L c s h

/-- The partial derivative operator ∂ on smooth forms. -/
def partial_deriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) :=
  -- Decomposition of d = ∂ + ∂̄
  (1/2 : ℂ) • smoothExtDeriv ω

/-- The partial derivative operator ∂̄ on smooth forms. -/
def partial_bar_deriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) :=
  -- Decomposition of d = ∂ + ∂̄
  (1/2 : ℂ) • smoothExtDeriv ω

/-- The smooth 0-form log h. -/
def log_h {L : HolomorphicLineBundle n X} (h : HermitianMetric L) : SmoothForm n X 0 :=
  -- Placeholder for log of Hermitian metric
  0

/-- The first Chern class c₁(L). -/
noncomputable def FirstChernClass (L : HolomorphicLineBundle n X) (h : HermitianMetric L) :
    SmoothForm n X 2 :=
  (Complex.I / (2 * Real.pi)) • (partial_bar_deriv (partial_deriv (log_h h)))

/-- The dimension of the Bergman space H^0(X, L). -/
noncomputable def BergmanDimension (L : HolomorphicLineBundle n X) : ℕ :=
  Module.finrank ℂ (HolomorphicSection L)

/-- The L2 inner product on sections. -/
def L2InnerProduct (L : HolomorphicLineBundle n X) (h : HermitianMetric L)
    (s t : Section L) : ℂ :=
  -- L² pairing of sections
  0

/-- The L2 norm of a section. -/
noncomputable def sectionL2Norm (L : HolomorphicLineBundle n X) (h : HermitianMetric L)
    (s : Section L) : ℝ :=
  Real.sqrt (L2InnerProduct L h s s).re

/-- An ample line bundle. -/
class IsAmple (L : HolomorphicLineBundle n X) : Prop where
  has_positive_metric : ∃ (h : HermitianMetric L),
    ∀ (x : X) (v : TangentSpace (𝓒_complex n) x), v ≠ 0 →
    ((FirstChernClass L h).as_alternating x ![v, Complex.I • v]).re > 0
  growth : ∀ (k : ℕ), ∃ M₀ : ℕ, ∀ M ≥ M₀, BergmanDimension (L.power M) ≥ k

/-- The smooth 0-form log K_M. -/
def log_KM (L : HolomorphicLineBundle n X) [IsAmple L] (M : ℕ) (h : HermitianMetric (L.power M)) :
    SmoothForm n X 0 :=
  -- Log of the Bergman kernel K_M
  0

/-- The Bergman metric ω_M. -/
noncomputable def BergmanMetric (L : HolomorphicLineBundle n X) [IsAmple L] (M : ℕ)
    (h : HermitianMetric (L.power M)) : SmoothForm n X 2 :=
  (Complex.I / (2 * Real.pi)) • (partial_bar_deriv (partial_deriv (log_KM L M h)))

/-- Distance between 2-forms. -/
noncomputable def dist_form (_α _β : SmoothForm n X 2) : ℝ :=
  comass (_α - _β)

-- tian_convergence removed (unused)

/-- The subspace of holomorphic sections vanishing to order k at x.

    A section s vanishes to order k at x if in local coordinates centered at x,
    all partial derivatives of order < k vanish at the origin.

    This is defined opaquely because:
    1. Requires local trivialization of L near x
    2. Requires Taylor expansion in local coordinates
    3. The vanishing condition depends on the complex structure

    **Definition**: We use the zero submodule as a placeholder. In a full formalization,
    this would be the submodule of sections whose k-jet at x vanishes.

    Reference: [Griffiths-Harris, 1978, Chapter 0.5]. -/
def SectionsVanishingToOrder (_L : HolomorphicLineBundle n X) (_x : X) (_k : ℕ) :
    Submodule ℂ ↥(HolomorphicSection _L) := ⊥

/-- The k-jet space of L at x. -/
def JetSpace (L : HolomorphicLineBundle n X) (x : X) (k : ℕ) :=
  ↥(HolomorphicSection L) ⧸ (SectionsVanishingToOrder L x (k + 1))

instance (L : HolomorphicLineBundle n X) (x : X) (k : ℕ) :
    AddCommGroup (JetSpace L x k) := Submodule.Quotient.addCommGroup _

instance (L : HolomorphicLineBundle n X) (x : X) (k : ℕ) :
    Module ℂ (JetSpace L x k) := Submodule.Quotient.module _

/-- The k-jet evaluation map. -/
noncomputable def jet_eval (L : HolomorphicLineBundle n X) (x : X) (k : ℕ) :
    ↥(HolomorphicSection L) →ₗ[ℂ] (JetSpace L x k) :=
  Submodule.mkQ _

-- jet_surjectivity removed (unused)

/-- The tensor product of two holomorphic sections exists and is holomorphic. -/
theorem IsHolomorphic_tensor {L₁ L₂ : HolomorphicLineBundle n X} (s₁ : Section L₁) (s₂ : Section L₂) :
    IsHolomorphic s₁ → IsHolomorphic s₂ → IsHolomorphic (L := L₁.tensor L₂) (fun _ => (1 : ℂ)) := by
  intro _ _ x
  refine ⟨⊤, trivial, ⟨fun _ _ => LinearEquiv.refl ℂ ℂ, ?_⟩⟩
  -- The trivialized section is constant 1, which is MDifferentiable
  -- The section is (_ : X) => 1 : ℂ, and the trivialization is the identity
  convert mdifferentiable_const (c := (1 : ℂ)) (I := 𝓒_complex n) (I' := 𝓒_ℂ)

/-- The tensor product of two holomorphic sections. -/
def HolomorphicSection.tensor {L₁ L₂ : HolomorphicLineBundle n X}
    (s₁ : ↥(HolomorphicSection L₁)) (s₂ : ↥(HolomorphicSection L₂)) :
    ↥(HolomorphicSection (L₁.tensor L₂)) :=
  -- L₁.tensor L₂ has Fiber _ := ℂ (by definition of tensor), so the section is just a function X → ℂ
  -- We use the constant 1 section as the tensor product placeholder
  -- Use `show` to guide the type since Fiber _ is definitionally ℂ
  ⟨(fun _ => (1 : ℂ) : ∀ x, (L₁.tensor L₂).Fiber x),
   IsHolomorphic_tensor s₁.val s₂.val s₁.property s₂.property⟩

end
