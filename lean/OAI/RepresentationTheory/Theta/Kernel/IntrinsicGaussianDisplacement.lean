import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiSchwartz

/-! # Intrinsic Gaussian Displacement -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianDisplacement.Intrinsic

noncomputable section

/-! The ray of a Heisenberg-translated positive Gaussian determines
the real displacement. Both injectivity steps use the actual Gaussian
formula and the positive imaginary matrix. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiSchwartz.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicParameter

theorem real_jacobi_injective {n : ℕ} (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin n))
    (q p r s : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) (h : IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi Z.matrix q p = IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi Z.matrix r s) :
    q = r ∧ p = s := by
  have him : (Z.matrix.map Complex.im).mulVec q = (Z.matrix.map Complex.im).mulVec r := by
    funext i
    have hi := congrArg Complex.im (congrFun h i)
    simp only [IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi,Complex.sub_im,Complex.ofReal_im,zero_sub,IntrinsicJacobiSchwartz.Intrinsic.mul_real_im] at hi
    exact neg_injective hi
  have hq : q = r := Matrix.mulVec_injective_of_isUnit Z.imaginary_posDef.isUnit him
  refine ⟨hq,?_⟩
  subst r
  funext i
  have hi := congrArg Complex.re (congrFun h i)
  simp only [IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi,Complex.sub_re,Complex.ofReal_re] at hi
  linarith

theorem gaussian_displacement_unique {n : ℕ} (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin n))
    (q p r s : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) (c : ℂ)
    (h : ∀ x, Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (Weil.Local.Gaussian.Construction.realCharacter 1) (Sum.elim q p) (Weil.Local.SiegelGaussian.Construction.siegelGaussian Z.matrix) x =
      c * Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (Weil.Local.Gaussian.Construction.realCharacter 1) (Sum.elim r s) (Weil.Local.SiegelGaussian.Construction.siegelGaussian Z.matrix) x) :
    q = r ∧ p = s := by
  apply real_jacobi_injective Z q p r s
  apply IntrinsicGaussianUniqueness.IntrinsicParameter.scaled_jacobi_parameter_unique Z.matrix _ _ (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor Z.matrix q p)
    (c * IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor Z.matrix r s) (Complex.exp_ne_zero _)
  intro x
  have hx := h x
  rw [IntrinsicGaussianUniqueness.IntrinsicHeisenberg.heisenberg_gaussian_formula Z.matrix Z.symmetric,
    IntrinsicGaussianUniqueness.IntrinsicHeisenberg.heisenberg_gaussian_formula Z.matrix Z.symmetric] at hx
  exact hx.trans (mul_assoc _ _ _).symm

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianDisplacement.Intrinsic
