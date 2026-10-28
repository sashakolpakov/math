import OAI.NumberTheory.ArithmeticGroups.Lattices.NormalizeOrthogonalBasis
import OAI.NumberTheory.ArithmeticGroups.Lattices.ReducedLatticeBasisExistence

/-! # Standard Siegel Matrix -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The bounded upper triangular matrix region supplied by lattice
basis reduction, with an orthogonal factor and positive diagonal. -/

open _root_.Module
open scoped Classical

def StandardSiegelMatrix.Construction.IsStandardSiegelMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (K U : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ),
    K ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
    (∀ i, 0 < a i) ∧
    (∀ i j, i.val + 1 = j.val → a i ≤ 2 * a j) ∧
    (∀ i j, j < i → U i j = 0) ∧
    (∀ i, U i i = 1) ∧
    (∀ i j, i < j → |U i j| ≤ 1 / 2) ∧
    M = K * Matrix.diagonal a * U

theorem FinSuccessorBasisLift.Construction.ReducedLatticeBasis.isStandardSiegelMatrix
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    {Λ : Submodule ℤ E} (d : FinSuccessorBasisLift.Construction.ReducedLatticeBasis Λ n) (b : OrthonormalBasis (Fin n) ℝ E) :
    StandardSiegelMatrix.Construction.IsStandardSiegelMatrix (b.toBasis.toMatrix (fun i => (d.latticeBasis i).val)) := by
  let q := NormalizeOrthogonalBasis.Construction.normalizedOrthogonalBasis d.orthogonalBasis d.orthogonal
  let K := b.toBasis.toMatrix q
  let U := d.orthogonalBasis.toMatrix (fun i => (d.latticeBasis i).val)
  let a : Fin n → ℝ := fun i => ‖d.orthogonalBasis i‖
  refine ⟨K, U, a, b.toMatrix_orthonormalBasis_mem_orthogonal q,
    (fun i => norm_pos_iff.mpr (d.orthogonalBasis.ne_zero i)), d.gap,
    (fun i j h => d.upper j i h), d.diagonal, (fun i j h => d.reduced j i h), ?_⟩
  have hq : b.toBasis.toMatrix d.orthogonalBasis = K * Matrix.diagonal a := by
    ext i j
    rw [Matrix.mul_diagonal]
    change b.repr (d.orthogonalBasis j) i = b.repr (q j) i * ‖d.orthogonalBasis j‖
    conv_lhs => rw [NormalizeOrthogonalBasis.Construction.orthogonalBasis_eq_norm_smul_normalized d.orthogonalBasis d.orthogonal j]
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [← hq]
  exact (b.toBasis.toMatrix_mul_toMatrix d.orthogonalBasis (fun i => (d.latticeBasis i).val)).symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
