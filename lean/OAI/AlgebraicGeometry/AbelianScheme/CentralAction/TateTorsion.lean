import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add

/-! # Tate Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateTorsion.Construction

noncomputable section

/-! Evaluation of the actual Tate inverse limit. Coherent q-divisions
lift every torsion point, and the evaluation kernel is q^n times Tate. -/

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add

variable (q : ℕ) [Fact q.Prime] {H : Type*} [AddCommGroup H]

def tateEvaluation (n : ℕ) : TateComparison.Add.Tate.Module (H := H) q →ₗ[ℤ_[q]] TateComparison.Add.Tate.torsion q H n where
  toFun x := x.val n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tate_transition_iterate (x : TateComparison.Add.Tate.Module (H := H) q) (n k : ℕ) :
    q ^ k • (x.val (n + k)).val = (x.val n).val := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := congrArg Subtype.val (x.property (n + k))
    change q • (x.val (n + k + 1)).val = (x.val (n + k)).val at ht
    rw [pow_succ', mul_nsmul, ← Nat.add_assoc, ht, ih]

def divisionChain (hdiv : ∀ x : H, ∃ y, q • y = x) (x : H) : ℕ → H
  | 0 => x
  | n + 1 => (hdiv (divisionChain hdiv x n)).choose

omit [Fact q.Prime] in
theorem divisionChain_step (hdiv : ∀ x : H, ∃ y, q • y = x) (x : H) (n : ℕ) :
    q • Construction.divisionChain q hdiv x (n + 1) = Construction.divisionChain q hdiv x n :=
  (hdiv (Construction.divisionChain q hdiv x n)).choose_spec

omit [Fact q.Prime] in
theorem divisionChain_iterate (hdiv : ∀ x : H, ∃ y, q • y = x) (x : H) (n : ℕ) :
    q ^ n • Construction.divisionChain q hdiv x n = x := by
  induction n with
  | zero => simp [Construction.divisionChain]
  | succ n ih => rw [pow_succ', mul_nsmul, divisionChain_step, ih]

/-- Divisibility of the actual point group supplies a coherent lift of
every q^n-torsion point, rather than an abstract rank assumption. -/
theorem tateEvaluation_surjective (hdiv : ∀ x : H, ∃ y, q • y = x) (n : ℕ) :
    Function.Surjective (tateEvaluation (H := H) q n) := by
  intro x
  let y : ∀ k, TateComparison.Add.Tate.torsion q H k := fun k =>
    ⟨q ^ n • Construction.divisionChain q hdiv x.val k, by
      change q ^ k • (q ^ n • Construction.divisionChain q hdiv x.val k) = 0
      rw [smul_comm, divisionChain_iterate]
      exact x.property⟩
  have hy : y ∈ TateComparison.Add.Tate.compatible (H := H) q := by
    intro k
    apply Subtype.ext
    change q • (q ^ n • Construction.divisionChain q hdiv x.val (k + 1)) =
      q ^ n • Construction.divisionChain q hdiv x.val k
    rw [smul_comm, divisionChain_step]
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  exact divisionChain_iterate q hdiv x.val n

/-- A Tate vector vanishing at level n is divisible by q^n in Tate.
The quotient vector is the shifted compatible sequence itself. -/
theorem tateEvaluation_kernel (n : ℕ) (x : TateComparison.Add.Tate.Module (H := H) q) :
    tateEvaluation q n x = 0 ↔ ∃ y : TateComparison.Add.Tate.Module (H := H) q, (q : ℤ_[q]) ^ n • y = x := by
  constructor
  · intro hx
    have hx0 : (x.val n).val = 0 := congrArg Subtype.val hx
    let y : ∀ k, TateComparison.Add.Tate.torsion q H k := fun k =>
      ⟨(x.val (n + k)).val, (tate_transition_iterate q x n k).trans hx0⟩
    have hy : y ∈ TateComparison.Add.Tate.compatible (H := H) q := by
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
    exact tate_transition_iterate q x k n
  · rintro ⟨y, rfl⟩
    rw [map_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    apply Subtype.ext
    exact (y.val n).property

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateTorsion.Construction
