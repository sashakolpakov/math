import OAI.NumberTheory.ArithmeticGroups.Lattices.BasisLift

/-! # Fin Successor Basis Lift -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FinSuccessorBasisLift.Construction

noncomputable section

section

/-! Indexing a lifted basis by Fin (n+1), with the new vector first. -/

open _root_.Module

def unitSumFinSuccEquiv (n : ℕ) : (Unit ⊕ Fin n) ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by intro x; cases x with
    | inl x => cases x; rfl
    | inr i => simp
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem basis_reindex_unitSumFinSucc_zero
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {n : ℕ} (b : Basis (Unit ⊕ Fin n) R M) :
    b.reindex (unitSumFinSuccEquiv n) 0 = b (Sum.inl ()) := by
  simp [Basis.reindex_apply, unitSumFinSuccEquiv]

theorem basis_reindex_unitSumFinSucc_succ
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {n : ℕ} (b : Basis (Unit ⊕ Fin n) R M) (i : Fin n) :
    b.reindex (unitSumFinSuccEquiv n) i.succ = b (Sum.inr i) := by
  simp [Basis.reindex_apply, unitSumFinSuccEquiv]

end

/-! Data for an integral lattice basis in a bounded upper triangular
position relative to an orthogonal real basis. -/

open _root_.Module

structure ReducedLatticeBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Λ : Submodule ℤ E) (n : ℕ) where
  latticeBasis : Basis (Fin n) ℤ Λ
  orthogonalBasis : Basis (Fin n) ℝ E
  orthogonal : Pairwise (fun i j => inner ℝ (orthogonalBasis i) (orthogonalBasis j) = 0)
  upper : ∀ i j, i < j → orthogonalBasis.repr (latticeBasis i).val j = 0
  diagonal : ∀ i, orthogonalBasis.repr (latticeBasis i).val i = 1
  reduced : ∀ i j, j < i → |orthogonalBasis.repr (latticeBasis i).val j| ≤ 1 / 2
  gap : ∀ i j, i.val + 1 = j.val → ‖orthogonalBasis i‖ ≤ 2 * ‖orthogonalBasis j‖

theorem ReducedLatticeBasis.first_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Λ : Submodule ℤ E} {n : ℕ} (d : ReducedLatticeBasis Λ n) (i : Fin n) (hi : i.val = 0) :
    (d.latticeBasis i).val = d.orthogonalBasis i := by
  apply d.orthogonalBasis.repr.injective
  ext j
  by_cases hij : i = j
  · subst j
    simpa using d.diagonal i
  · have hij' : i < j := by
      have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      omega
    rw [d.upper i j hij', Basis.repr_self_apply]
    simp [hij]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FinSuccessorBasisLift.Construction
