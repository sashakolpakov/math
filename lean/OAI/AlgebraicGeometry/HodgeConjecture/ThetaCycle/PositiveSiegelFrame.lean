import OAI.RepresentationTheory.Weil.Local.SiegelGaussian
import OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix

/-! # Positive Siegel Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PositiveSiegelFrame.CM

noncomputable section

/-! ThetaCycle: each actual Siegel matrix gives the native positive Lagrangian
frame [1;Z], with its literal Gaussian quadratic matrix. -/

open scoped Classical MatrixOrder ComplexOrder
open _root_.Matrix OAI.RepresentationTheory.Weil.Local.SiegelGaussian.Construction

theorem positive_real_matrix_complexification {I : Type*} [Fintype I] [DecidableEq I]
    (Y : Matrix I I ℝ) (hY : Y.PosDef) : (Y.map Complex.ofRealHom).PosDef := by
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg
  have hPY : P.transpose * P = Y := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hP.symm
  have hdet : P.det ≠ 0 := by
    intro hz
    have hy := hY.det_pos
    rw [← hPY, Matrix.det_mul, Matrix.det_transpose, hz, zero_mul] at hy
    exact (lt_irrefl 0) hy
  have hunit : IsUnit (P.map Complex.ofRealHom) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    change IsUnit (Complex.ofRealHom.mapMatrix P).det
    rw [← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr hdet).map Complex.ofRealHom
  have hconj : (P.map Complex.ofRealHom).conjTranspose = P.transpose.map Complex.ofRealHom := by
    ext i j
    exact Complex.conj_ofReal _
  rw [← hPY, Matrix.map_mul, ← hconj]
  exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit hunit)

def siegelPositiveFrame {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) : RepresentationTheory.Weil.Local.SiegelGaussian.Construction.PositiveLagrangianFrame N where
  matrix := Matrix.fromRows 1 Z.matrix
  isotropic := by
    simp only [Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.J, Matrix.mul_assoc,
      Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows, zero_mul, neg_mul,
      one_mul, mul_one, zero_add, add_zero, Z.symmetric.eq, neg_add_cancel]
  positive := by
    convert! (positive_real_matrix_complexification _ Z.imaginary_posDef).smul
      (by norm_num : (0 : ℝ) < 2) using 1
    simp only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.conjTranspose_one,
      Matrix.J, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows,
      zero_mul, neg_mul, one_mul, mul_one, zero_add, add_zero]
    rw [add_comm, ← sub_eq_add_neg]
    exact RepresentationTheory.Weil.Local.SiegelGaussian.Construction.symmetric_complex_imaginary_gram Z.matrix Z.symmetric

theorem siegel_positive_frame_position {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    (siegelPositiveFrame Z).position = 1 := rfl

theorem siegel_positive_frame_momentum {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    (siegelPositiveFrame Z).momentum = Z.matrix := rfl

theorem siegel_positive_frame_quadratic {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    (siegelPositiveFrame Z).quadraticMatrix = Z.matrix := by
  change Z.matrix * (1 : Matrix (Fin N) (Fin N) ℂ)⁻¹ = Z.matrix
  rw [inv_one, mul_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PositiveSiegelFrame.CM
