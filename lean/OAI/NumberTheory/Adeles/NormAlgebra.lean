import Mathlib

/-! # Norm Algebra -/

namespace OAI.NumberTheory.Adeles.NormAlgebra.CompletionFactors

noncomputable section

/-! Determinant-norm identities for scalar extension and finite products. -/

open scoped TensorProduct Classical

theorem norm_baseChange
    {R A S : Type*} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Module.Free R S] [Module.Finite R S] (x : S) :
    Algebra.norm A (1 ⊗ₜ[R] x : A ⊗[R] S) = algebraMap R A (Algebra.norm R x) := by
  have hm : Algebra.lmul A (A ⊗[R] S) (1 ⊗ₜ[R] x) =
      (Algebra.lmul R S x).baseChange A := by
    ext a
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, hm, LinearMap.det_baseChange]
  rfl

theorem det_dependent_blockDiagonal
    {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]
    {n : ι → Type*} [∀ i, Fintype (n i)] (M : ∀ i, Matrix (n i) (n i) R) :
    (Matrix.blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  rw [(Matrix.blockTriangular_blockDiagonal' M).det_fintype]
  apply Finset.prod_congr rfl
  intro i _
  let e : n i ≃ {p : Sigma n // p.1 = i} :=
    { toFun := fun a => ⟨⟨i, a⟩, rfl⟩
      invFun := fun p => p.property ▸ p.val.2
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨j, a⟩, h⟩
        cases h
        rfl }
  calc
    ((Matrix.blockDiagonal' M).toSquareBlock Sigma.fst i).det =
        (((Matrix.blockDiagonal' M).toSquareBlock Sigma.fst i).submatrix e e).det :=
      (Matrix.det_submatrix_equiv_self e _).symm
    _ = (M i).det := by
      congr 1
      ext a b
      exact Matrix.blockDiagonal'_apply_eq M i a b

theorem norm_pi
    {ι R : Type*} [Fintype ι] [CommRing R]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] (x : ∀ i, S i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let b := fun i => Module.Free.chooseBasis R (S i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis b)]
  have hm : Algebra.leftMulMatrix (Pi.basis b) x =
      Matrix.blockDiagonal' (fun i => Algebra.leftMulMatrix (b i) (x i)) := by
    ext ⟨i, a⟩ ⟨j, c⟩
    by_cases h : i = j
    · subst j
      simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]
    · simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply,
        Matrix.blockDiagonal'_apply', h]
  rw [hm, det_dependent_blockDiagonal]
  apply Finset.prod_congr rfl
  intro i _
  exact (Algebra.norm_eq_matrix_det (b i) (x i)).symm

end

end OAI.NumberTheory.Adeles.NormAlgebra.CompletionFactors
