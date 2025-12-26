import Hodge.Analytic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic

noncomputable section

open Classical Filter

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-!
# Track A.2: Federer-Fleming Compactness Theorem

This file formalizes the Federer-Fleming compactness theorem for integral currents.

## Mathematical Statement
The space of integral currents with bounded mass and boundary mass is
compact in the flat norm topology.

## Reference
[Federer-Fleming, "Normal and Integral Currents", Ann. Math 1960]
-/

/-- The flat norm of a current T. 
Defined as the infimum of M(S) + M(G) over all decompositions T = S + ∂G. -/
def flatNorm {k : ℕ} (T : Current n X k) : ℝ :=
  sInf { r : ℝ | ∃ (S : Current n X k) (G : Current n X (k + 1)),
    T = S + G.boundary ∧ r = S.mass + G.mass }

/-- The hypothesis bundle for Federer-Fleming compactness. -/
structure FFCompactnessHypothesis (k : ℕ) where
  /-- The sequence of integral currents -/
  T : ℕ → IntegralCurrent n X k
  /-- Uniform mass bound -/
  M : ℝ
  /-- Each current has mass + boundary mass bounded by M -/
  mass_bound : ∀ j, (T j : Current n X k).mass + (extDeriv (T j : Current n X k)).mass ≤ M

/-- The conclusion of Federer-Fleming: existence of a convergent subsequence. -/
structure FFCompactnessConclusion (k : ℕ) (hyp : FFCompactnessHypothesis k) where
  /-- The limit current (also integral) -/
  T_limit : IntegralCurrent n X k
  /-- The extraction function (subsequence) -/
  φ : ℕ → ℕ
  /-- The extraction is strictly increasing -/
  φ_strict_mono : StrictMono φ
  /-- Flat norm convergence to the limit -/
  converges : Tendsto (fun j => flatNorm ((hyp.T (φ j) : Current n X k) - T_limit.toFun)) atTop (nhds 0)

/-- **The Deformation Theorem** (Federer-Fleming 1960, 4.2)
Any integral current T can be approximated by a polyhedral current P on a grid
of size ε, with bounds on the error in flat norm. -/
theorem deformation_theorem {k : ℕ} (T : IntegralCurrent n X k) (ε : ℝ) (hε : ε > 0) :
    ∃ (P : IntegralCurrent n X k) (Q : IntegralCurrent n X (k + 1)) (S : IntegralCurrent n X k),
      (T : Current n X k) = P + boundary Q + S ∧
      (P : Current n X k).mass ≤ C1 n k * ((T : Current n X k).mass + ε * (extDeriv (T : Current n X k)).mass) ∧
      (extDeriv (P : Current n X k)).mass ≤ C2 n k * (extDeriv (T : Current n X k)).mass ∧
      (Q : Current n X (k + 1)).mass ≤ C3 n k * ε * (T : Current n X k).mass ∧
      (S : Current n X k).mass ≤ C4 n k * ε * (extDeriv (T : Current n X k)).mass :=
  sorry

/-- Auxiliary constants for the Deformation Theorem.
Reference: [Federer-Fleming 1960, 4.2]. -/
noncomputable def C1 (n k : ℕ) : ℝ := 2 ^ n * (n + 1)
noncomputable def C2 (n k : ℕ) : ℝ := 2 ^ n * (n + 1)
noncomputable def C3 (n k : ℕ) : ℝ := 2 ^ n * (n + 1)
noncomputable def C4 (n k : ℕ) : ℝ := 2 ^ n * (n + 1)

theorem federer_fleming_compactness {k : ℕ}
    (hyp : FFCompactnessHypothesis k) :
    FFCompactnessConclusion k hyp := by
  -- 1. Discretization: Use the Deformation Theorem to find a sequence of
  -- polyhedral currents P_n that are flat-norm close to T_n.
  have h_discretize : ∀ (n_idx : ℕ) (m : ℕ), m > 0 → ∃ (P : IntegralCurrent n X k),
      flatNorm ((hyp.T n_idx : Current n X k) - P) < (1 : ℝ) / m := by
    intro n_idx m hm
    let ε := (1 : ℝ) / (m * (C3 n k + C4 n k * (hyp.M + 1)))
    have hε : ε > 0 := by
      apply div_pos zero_lt_one
      apply mul_pos (Nat.cast_pos.mpr hm)
      apply add_pos_of_pos_of_nonneg
      · apply add_pos_of_pos_of_nonneg
        · dsimp [C3]; apply div_pos zero_lt_one; exact Nat.cast_pos.mpr (Nat.factorial_pos k)
        · dsimp [C4]; linarith
      · apply mul_nonneg (by dsimp [C4]; linarith) (by linarith [hyp.M_pos]) -- M + 1 > 0
    obtain ⟨P, Q, S, h_decomp, hP_mass, hP_boundary, hQ_mass, hS_mass⟩ := deformation_theorem (hyp.T n_idx) ε hε
    use P
    rw [h_decomp]
    have : (P : Current n X k) + boundary Q + S - P = boundary Q + S := by abel
    rw [this]
    calc flatNorm (boundary Q + S) ≤ flatNorm (boundary Q) + flatNorm S := flatNorm_add_le _ _
      _ ≤ (Q : Current n X (k + 1)).mass + (S : Current n X k).mass := by
        apply add_le_add
        · -- flatNorm(∂Q) ≤ mass(Q) by definition of flat norm as infimum
          unfold flatNorm
          apply sInf_le
          · use 0; simp [Current.mass_zero]
          · use Q; simp
        · exact flatNorm_le_mass S
      _ ≤ (C3 n k * ε * (hyp.T n_idx : Current n X k).mass) + (C4 n k * ε * (extDeriv (hyp.T n_idx : Current n X k)).mass) := add_le_add hQ_mass hS_mass
      _ ≤ (C3 n k * ε * hyp.M) + (C4 n k * ε * hyp.M) := by
        -- Since mass(T) + mass(∂T) ≤ M, both mass(T) and mass(∂T) are ≤ M.
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left (by linarith [hyp.mass_bound n_idx])
          apply mul_nonneg (by dsimp [C3]; linarith) (le_of_lt hε)
        · apply mul_le_mul_of_nonneg_left (by linarith [hyp.mass_bound n_idx])
          apply mul_nonneg (by dsimp [C4]; linarith) (le_of_lt hε)
      _ = ε * hyp.M * (C3 n k + C4 n k) := by ring
      _ < (1 : ℝ) / m := by
        -- choice of ε = 1 / (m * (C3 n k + C4 n k * (hyp.M + 1)))
        -- ε * M * (C3 + C4) = (M * (C3 + C4)) / (m * (C3 + C4 * (M + 1)))
        -- which is < 1/m because M * (C3 + C4) < C3 + C4 * (M + 1)
        rw [mul_assoc, ← mul_add]
        unfold_let ε
        field_simp
        apply (div_lt_div_iff_of_pos_right _).mpr
        · nlinarith [hyp.M_pos]
        · apply mul_pos (Nat.cast_pos.mpr hm)
          nlinarith [hyp.M_pos]

  -- 2. Compactness for polyhedral currents on a fixed lattice.
  -- Bounded sequences of polyhedral currents have convergent subsequences.
  -- This follows from the finiteness of the lattice cells and bounded coefficients.
  have h_poly_compact : ∀ (ε_val : ℝ) (hε_val : ε_val > 0) (P : ℕ → IntegralCurrent n X k) (M_val : ℝ),
      (∀ j, (P j : Current n X k).mass ≤ M_val) →
      (∃ (L : CubicalLattice n X ε_val), ∀ j, isPolyhedral (P j) L) →
      ∃ (P_limit : IntegralCurrent n X k) (φ_sub : ℕ → ℕ),
        StrictMono φ_sub ∧
        Tendsto (fun j => flatNorm ((P (φ_sub j) : Current n X k) - P_limit)) atTop (nhds 0) := by
    intro ε_val hε_val P M_val hM_val ⟨L, hL⟩
    -- A polyhedral current on a fixed finite lattice L is identified with a vector 
    -- in the finite-dimensional space ℝ^N, where N is the number of k-cells.
    -- The coefficients are integers because P j are integral currents.
    -- The mass bound M implies the integer coefficients are bounded.
    -- A bounded subset of ℤ^N is finite.
    -- By the pigeonhole principle, any sequence in a finite set has a constant subsequence.
    -- A constant subsequence clearly converges in flat norm.
    sorry

  -- 3. Diagonal Argument: Combine discretization and polyhedral compactness.
  -- For each m ≥ 1, let ε_m = 1/m.
  -- We have sequences of polyhedral currents P_{n,m} such that F(T_n - P_{n,m}) < 1/m.
  -- Use h_poly_compact to extract a subsequential limit for m=1, then a further subsequence
  -- for m=2, and so on.
  -- Let ψ_m be the subsequence for the m-th stage.
  -- The diagonal subsequence φ(n) = ψ_n(n) is the required extraction.
  -- The limit current T_limit is the limit of the P_{φ(n), n} in flat norm.
  have ∃ (T_limit : IntegralCurrent n X k) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (fun j => flatNorm ((hyp.T (φ j) : Current n X k) - T_limit.toFun)) atTop (nhds 0) := by
    -- Every Cauchy sequence in the flat norm space of integral currents with bounded mass
    -- converges to an integral current (Completeness of Integral Currents).
    sorry
  obtain ⟨T_limit, φ, hφ, h_conv⟩ := this
  exact ⟨T_limit, φ, hφ, h_conv⟩

end
