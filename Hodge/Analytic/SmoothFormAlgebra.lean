import Hodge.Basic

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]

instance (k : ℕ) : Zero (SmoothForm n X k) where
  zero := ⟨fun _ => 0⟩

instance (k : ℕ) : Add (SmoothForm n X k) where
  add ω η := ⟨fun x => ω.as_alternating x + η.as_alternating x⟩

instance (k : ℕ) : Neg (SmoothForm n X k) where
  neg ω := ⟨fun x => -ω.as_alternating x⟩

instance (k : ℕ) : SMul ℂ (SmoothForm n X k) where
  smul c ω := ⟨fun x => c • ω.as_alternating x⟩

instance (k : ℕ) : SMul ℝ (SmoothForm n X k) where
  smul r ω := ⟨fun x => (r : ℂ) • ω.as_alternating x⟩

@[simp] lemma SmoothForm.zero_apply (k : ℕ) (x : X) : (0 : SmoothForm n X k).as_alternating x = 0 := rfl
@[simp] lemma SmoothForm.add_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) :
  (ω + η).as_alternating x = ω.as_alternating x + η.as_alternating x := rfl
@[simp] lemma SmoothForm.neg_apply (k : ℕ) (ω : SmoothForm n X k) (x : X) :
  (-ω).as_alternating x = -ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_apply (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) (x : X) :
  (c • ω).as_alternating x = c • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_real_apply (k : ℕ) (r : ℝ) (ω : SmoothForm n X k) (x : X) :
  (r • ω).as_alternating x = (r : ℂ) • ω.as_alternating x := rfl

instance (k : ℕ) : AddCommGroup (SmoothForm n X k) where
  add_assoc α β γ := by ext x v; simp [add_assoc]
  zero_add α := by ext x v; simp
  add_zero α := by ext x v; simp
  add_comm α β := by ext x v; simp [add_comm]
  neg_add_cancel α := by ext x v; simp
  nsmul n α := ⟨fun x => n • α.as_alternating x⟩
  nsmul_zero α := by ext x v; simp
  nsmul_succ n α := by ext x v; simp [add_smul, one_smul, add_comm]
  zsmul z α := ⟨fun x => z • α.as_alternating x⟩
  zsmul_zero' α := by ext x v; simp
  zsmul_succ' n α := by ext x v; simp [add_smul, one_smul, add_comm]
  zsmul_neg' n α := by ext x v; simp [Int.negSucc_eq, add_smul, one_smul]; ring_nf
  sub α β := α + -β
  sub_eq_add_neg α β := rfl

instance (k : ℕ) : Module ℂ (SmoothForm n X k) where
  one_smul α := by ext x v; simp
  mul_smul r s α := by ext x v; simp [mul_smul]
  smul_zero r := by ext x v; simp
  smul_add r α β := by ext x v; simp [smul_add]
  add_smul r s α := by ext x v; simp [add_smul]
  zero_smul α := by ext x v; simp

instance (k : ℕ) : Module ℝ (SmoothForm n X k) where
  one_smul α := by ext x v; simp
  mul_smul r s α := by ext x v; simp [mul_smul]
  smul_zero r := by ext x v; simp
  smul_add r α β := by ext x v; simp [smul_add]
  add_smul r s α := by ext x v; simp [add_smul]
  zero_smul α := by ext x v; simp

end
