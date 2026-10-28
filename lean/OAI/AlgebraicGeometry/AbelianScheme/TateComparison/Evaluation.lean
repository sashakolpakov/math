import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor

/-! # Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate

noncomputable section

/-! Evaluation of the actual inverse limit and its q-power kernel. A
divisible point group gives all torsion points as Tate evaluations. -/

universe u
variable (q : ℕ) [Fact q.Prime] {H : Type u} [AddCommGroup H]

def evaluate (n : ℕ) : Add.Tate.Module (H := H) q →ₗ[ℤ_[q]] Add.Tate.torsion q H n where
  toFun x := x.val n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def divisionChain (hdiv : ∀ x : H, ∃ y, q • y = x) (x : H) : ℕ → H
  | 0 => x
  | n + 1 => (hdiv (divisionChain hdiv x n)).choose

omit [Fact q.Prime] in
theorem divisionChain_step (hdiv : ∀ x : H, ∃ y, q • y = x) (x : H) (n : ℕ) :
    q • Tate.divisionChain q hdiv x (n + 1) = Tate.divisionChain q hdiv x n :=
  (hdiv (Tate.divisionChain q hdiv x n)).choose_spec

omit [Fact q.Prime] in
theorem divisionChain_iterate (hdiv : ∀ x : H, ∃ y, q • y = x) (x : H) (n : ℕ) :
    q ^ n • Tate.divisionChain q hdiv x n = x := by
  induction n with
  | zero => simp [Tate.divisionChain]
  | succ n ih => rw [pow_succ', mul_nsmul, divisionChain_step, ih]

theorem evaluate_surjective (hdiv : ∀ x : H, ∃ y, q • y = x) (n : ℕ) :
    Function.Surjective (evaluate (H := H) q n) := by
  intro x
  let y : ∀ k, Add.Tate.torsion q H k := fun k =>
    ⟨q ^ n • Tate.divisionChain q hdiv x.val k, by
      change q ^ k • (q ^ n • Tate.divisionChain q hdiv x.val k) = 0
      rw [smul_comm, divisionChain_iterate]
      exact x.property⟩
  have hy : y ∈ Add.Tate.compatible (H := H) q := by
    intro k
    apply Subtype.ext
    change q • (q ^ n • Tate.divisionChain q hdiv x.val (k + 1)) =
      q ^ n • Tate.divisionChain q hdiv x.val k
    rw [smul_comm, divisionChain_step]
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  exact divisionChain_iterate q hdiv x.val n

theorem evaluate_eq_zero_iff (n : ℕ) (x : Add.Tate.Module (H := H) q) :
    evaluate q n x = 0 ↔ ∃ y : Add.Tate.Module (H := H) q, (q : ℤ_[q]) ^ n • y = x := by
  constructor
  · intro hx
    have hx0 : (x.val n).val = 0 := congrArg Subtype.val hx
    let y : ∀ k, Add.Tate.torsion q H k := fun k =>
      ⟨(x.val (n + k)).val, (Functor.Tate.transition_iterate q x n k).trans hx0⟩
    have hy : y ∈ Add.Tate.compatible (H := H) q := by
      intro k
      apply Subtype.ext
      have ht := congrArg Subtype.val (x.property (n + k))
      change q • (x.val (n + k + 1)).val = (x.val (n + k)).val at ht
      change q • (x.val (n + (k + 1))).val = (x.val (n + k)).val
      rw [← Nat.add_assoc]
      exact ht
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    funext k
    apply Subtype.ext
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    change q ^ n • (x.val (n + k)).val = (x.val k).val
    rw [Nat.add_comm n k]
    exact Functor.Tate.transition_iterate q x k n
  · rintro ⟨y, rfl⟩
    rw [map_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    apply Subtype.ext
    exact (y.val n).property

def torsionQuotientEquiv (hdiv : ∀ x : H, ∃ y, q • y = x) (n : ℕ) :
    (Add.Tate.Module (H := H) q ⧸ (evaluate (H := H) q n).ker) ≃ₗ[ℤ_[q]] Add.Tate.torsion q H n :=
  (evaluate q n).quotKerEquivOfSurjective (evaluate_surjective q hdiv n)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate
