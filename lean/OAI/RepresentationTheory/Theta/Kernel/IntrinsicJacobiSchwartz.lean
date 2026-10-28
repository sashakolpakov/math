import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness

/-! # Intrinsic Jacobi Schwartz -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiSchwartz.Intrinsic

noncomputable section

/-! Every complex Jacobi variable is represented by a real Heisenberg
translate. The resulting Gaussian is an actual native Schwartz test. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg

theorem mul_real_re {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (q : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) (i : Fin n) :
    (Z.mulVec (fun j => (q j : ℂ)) i).re = (Z.map Complex.re).mulVec q i := by
  simp [Matrix.mulVec,dotProduct,Complex.mul_re]

theorem mul_real_im {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (q : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) (i : Fin n) :
    (Z.mulVec (fun j => (q j : ℂ)) i).im = (Z.map Complex.im).mulVec q i := by
  simp [Matrix.mulVec,dotProduct,Complex.mul_im]

theorem real_jacobi_surjective {n : ℕ} (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin n)) (ξ : Fin n → ℂ) :
    ∃ q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n, IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi Z.matrix q p = ξ := by
  let Y : Matrix (Fin n) (Fin n) ℝ := Z.matrix.map Complex.im
  let q : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n := Y⁻¹.mulVec (fun i => -(ξ i).im)
  let p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n := fun i => (ξ i).re + (Z.matrix.map Complex.re).mulVec q i
  have hY : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp Z.imaginary_posDef.isUnit
  have hq : Y.mulVec q = fun i => -(ξ i).im := by
    change Y.mulVec (Y⁻¹.mulVec (fun i => -(ξ i).im)) = _
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv Y hY,Matrix.one_mulVec]
  refine ⟨q,p,?_⟩
  funext i
  apply Complex.ext
  · change p i - (Z.matrix.mulVec (fun j => (q j : ℂ)) i).re = (ξ i).re
    rw [mul_real_re]
    change (ξ i).re + (Z.matrix.map Complex.re).mulVec q i - (Z.matrix.map Complex.re).mulVec q i = _
    ring
  · simp only [IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi, Complex.sub_im, Complex.ofReal_im, zero_sub]
    rw [mul_real_im]
    change -(Y.mulVec q i) = _
    rw [hq,neg_neg]

theorem jacobi_gaussian_test_exists {n : ℕ} (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin n))
    (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (hφ : φ.val = Weil.Local.SiegelGaussian.Construction.siegelGaussian Z.matrix) (ξ : Fin n → ℂ) :
    ∃ φξ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n, φξ.val = IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian Z.matrix ξ := by
  obtain ⟨q,p,hξ⟩ := real_jacobi_surjective Z ξ
  refine ⟨(IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor Z.matrix q p)⁻¹ • IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftedGaussianTest φ q p,?_⟩
  funext x
  change (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor Z.matrix q p)⁻¹ * (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftedGaussianTest φ q p).val x = _
  have hs : IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor Z.matrix q p ≠ 0 := Complex.exp_ne_zero _
  rw [IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shifted_gaussian_test_value Z.matrix Z.symmetric φ hφ,hξ,← mul_assoc,
    inv_mul_cancel₀ hs,one_mul]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiSchwartz.Intrinsic
