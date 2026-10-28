import OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates

/-! # Siegel Restriction -/

namespace OAI.RepresentationTheory.Theta.Adelic.SiegelRestriction

noncomputable section

/-! Restricting a positive Siegel quadratic form along an injective real
linear map produces the actual positive Gaussian form on that subspace. -/

open scoped Classical

open _root_.Matrix

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def realCongruence (T : Matrix I J ℝ) (Z : Matrix I I ℂ) : Matrix J J ℂ :=
  (T.map Complex.ofRealHom).transpose * Z * T.map Complex.ofRealHom

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem realCongruence_symmetric (T : Matrix I J ℝ) (Z : Matrix I I ℂ) (hZ : Z.IsSymm) :
    (realCongruence T Z).IsSymm := by
  change (realCongruence T Z).transpose = realCongruence T Z
  simp only [realCongruence, Matrix.transpose_mul, Matrix.transpose_transpose,
    hZ.eq, Matrix.mul_assoc]

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem realCongruence_imaginary (T : Matrix I J ℝ) (Z : Matrix I I ℂ) :
    (fun i j => (realCongruence T Z i j).im) =
      T.transpose * (show Matrix I I ℝ from fun i j => (Z i j).im) * T := by
  ext i j
  simp only [realCongruence, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Complex.ofRealHom_eq_coe, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add]
  rfl

def restrictedSiegel (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (T : Matrix I J ℝ)
    (hT : Function.Injective T.mulVec) : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J where
  matrix := realCongruence T Z.matrix
  symmetric := realCongruence_symmetric T Z.matrix Z.symmetric
  imaginary_posDef := by
    rw [realCongruence_imaginary]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Z.imaginary_posDef.conjTranspose_mul_mul_same hT

theorem realCongruence_form (T : Matrix I J ℝ) (Z : Matrix I I ℂ) (x y : J → ℝ) :
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (realCongruence T Z) x y = AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z (T.mulVec x) (T.mulVec y) := by
  have hb {L : Type} [Fintype L] [DecidableEq L] (M : Matrix L L ℂ) (u v : L → ℝ) :
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm M u v = M.toBilin' (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) := by
    simp only [AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, Matrix.toBilin'_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hT (u : J → ℝ) : (T.map Complex.ofRealHom).mulVec (fun i => (u i : ℂ)) =
      fun i => (T.mulVec u i : ℂ) := by
    funext i
    exact (Complex.ofRealHom.map_mulVec T u i).symm
  rw [hb, hb, realCongruence, ← Matrix.toBilin'_comp]
  change Z.toBilin' ((T.map Complex.ofRealHom).mulVec (fun i => (x i : ℂ)))
    ((T.map Complex.ofRealHom).mulVec (fun i => (y i : ℂ))) = _
  rw [hT, hT]

end

end OAI.RepresentationTheory.Theta.Adelic.SiegelRestriction
