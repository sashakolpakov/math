import OAI.NumberTheory.ArithmeticGroups.Lattices.FinSuccessorBasisLift
import Mathlib.LinearAlgebra.Basis.SMul

/-! # Normalize Orthogonal Basis -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NormalizeOrthogonalBasis.Construction

noncomputable section

/-! Normalize an orthogonal basis while retaining its positive
diagonal scaling factors. -/

open _root_.Module

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

omit [Fintype ι] in
theorem orthogonal_basis_normalized_orthonormal (b : Basis ι ℝ E)
    (hb : Pairwise (fun i j => inner ℝ (b i) (b j) = 0)) :
    Orthonormal ℝ (fun i => ‖b i‖⁻¹ • b i) := by
  constructor
  · intro i
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (b.ne_zero i))]
  · intro i j hij
    rw [real_inner_smul_left, real_inner_smul_right, hb hij, mul_zero, mul_zero]

def normalizedOrthogonalBasis (b : Basis ι ℝ E)
    (hb : Pairwise (fun i j => inner ℝ (b i) (b j) = 0)) : OrthonormalBasis ι ℝ E :=
  (b.isUnitSMul (fun i => isUnit_iff_ne_zero.mpr
    (inv_ne_zero (norm_ne_zero_iff.mpr (b.ne_zero i))))).toOrthonormalBasis (by
      convert orthogonal_basis_normalized_orthonormal b hb using 1
      funext i
      exact Basis.isUnitSMul_apply _ i)

theorem normalizedOrthogonalBasis_apply (b : Basis ι ℝ E)
    (hb : Pairwise (fun i j => inner ℝ (b i) (b j) = 0)) (i : ι) :
    normalizedOrthogonalBasis b hb i = ‖b i‖⁻¹ • b i := by
  simp [normalizedOrthogonalBasis, Basis.coe_toOrthonormalBasis, Basis.isUnitSMul_apply]

theorem orthogonalBasis_eq_norm_smul_normalized (b : Basis ι ℝ E)
    (hb : Pairwise (fun i j => inner ℝ (b i) (b j) = 0)) (i : ι) :
    b i = ‖b i‖ • normalizedOrthogonalBasis b hb i := by
  rw [normalizedOrthogonalBasis_apply, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (b.ne_zero i)), one_smul]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NormalizeOrthogonalBasis.Construction
