import OAI.RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice

/-! # Factorization -/

namespace OAI.RepresentationTheory.Theta.Factorization.Derivative

noncomputable section

/-! Tensor inputs and block-diagonal periods multiply completed theta sums. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def tensorInput (φ : DerivativeFactorizationDefinitions.Input ι) (ψ : DerivativeFactorizationDefinitions.Input κ) : DerivativeFactorizationDefinitions.Input (Sum ι κ) := by
  let f : (ι → DerivativeFactorizationDefinitions.AQf) × (κ → DerivativeFactorizationDefinitions.AQf) → ℂ := fun a => φ.1 a.1 * ψ.1 a.2
  have hf : IsLocallyConstant f :=
    (φ.2.1.comp_continuous continuous_fst).mul
      (ψ.2.1.comp_continuous continuous_snd)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact (φ.2.2.prod ψ.2.2)
    intro a ha
    exact ⟨subset_tsupport φ.1 (mul_ne_zero_iff.mp ha).1,
      subset_tsupport ψ.1 (mul_ne_zero_iff.mp ha).2⟩
  exact ⟨f ∘ Homeomorph.sumArrowHomeomorphProdArrow,
    hf.comp_continuous Homeomorph.sumArrowHomeomorphProdArrow.continuous,
    hc.comp_homeomorph Homeomorph.sumArrowHomeomorphProdArrow⟩

omit [Fintype ι] [Fintype κ] in
theorem tensorInput_apply (φ : DerivativeFactorizationDefinitions.Input ι) (ψ : DerivativeFactorizationDefinitions.Input κ) (a : Sum ι κ → DerivativeFactorizationDefinitions.AQf) :
    (tensorInput φ ψ).1 a =
      φ.1 (fun i => a (Sum.inl i)) * ψ.1 (fun j => a (Sum.inr j)) := rfl

theorem kernel_block (B₁ : Matrix ι ι ℂ) (B₂ : Matrix κ κ ℂ)
    (x₁ : ι → ℚ) (x₂ : κ → ℚ) (z₁ : ι → ℂ) (z₂ : κ → ℂ) :
    DerivativeFactorizationDefinitions.kernel (fromBlocks B₁ 0 0 B₂) (Sum.elim x₁ x₂) (Sum.elim z₁ z₂) =
      DerivativeFactorizationDefinitions.kernel B₁ x₁ z₁ * DerivativeFactorizationDefinitions.kernel B₂ x₂ z₂ := by
  simp only [DerivativeFactorizationDefinitions.kernel, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply,
    Fintype.sum_sum_type, DerivativeFactorizationDefinitions.realPosition, Sum.elim_inl, Sum.elim_inr,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    zero_add, add_zero, Finset.sum_add_distrib]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem completionForm_block (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ)
    (Z₁₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Sum ι κ))
    (hZ : Z₁₂.matrix = fromBlocks Z₁.matrix 0 0 Z₂.matrix)
    (z₁ : ι → ℂ) (z₂ : κ → ℂ) :
    Z₁₂.completionForm (Sum.elim z₁ z₂) (Sum.elim z₁ z₂) =
      Z₁.completionForm z₁ z₁ + Z₂.completionForm z₂ z₂ := by
  have hIm : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₁₂.matrix =
      fromBlocks (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₁.matrix) 0 0 (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₂.matrix) := by
    rw [hZ, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary, fromBlocks_map]
    simp only [Matrix.map_zero, Complex.zero_im, Complex.ofReal_zero]
    rfl
  have hinv : (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₁₂.matrix)⁻¹ =
      fromBlocks (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₁.matrix)⁻¹ 0 0 (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₂.matrix)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hIm, fromBlocks_multiply]
    simp only [Matrix.mul_nonsing_inv _ Z₁.matrixImaginary_det_isUnit,
      Matrix.mul_nonsing_inv _ Z₂.matrixImaginary_det_isUnit,
      Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, fromBlocks_one]
  rw [AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.completionForm_quadratic,
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.completionForm_quadratic, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.completionForm_quadratic, hinv]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero]
  ring

theorem theta_block (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ)
    (φ₁ : DerivativeFactorizationDefinitions.Input ι) (φ₂ : DerivativeFactorizationDefinitions.Input κ) (z₁ : ι → ℂ) (z₂ : κ → ℂ) :
    DerivativeFactorizationDefinitions.theta (tensorInput φ₁ φ₂) (fromBlocks Z₁.matrix 0 0 Z₂.matrix)
        (Sum.elim z₁ z₂) =
      DerivativeFactorizationDefinitions.theta φ₁ Z₁.matrix z₁ * DerivativeFactorizationDefinitions.theta φ₂ Z₂.matrix z₂ := by
  rw [DerivativeFactorizationDefinitions.theta, DerivativeFactorizationDefinitions.theta, DerivativeFactorizationDefinitions.theta, tsum_mul_tsum_of_summable_norm
    (DerivativeFactorizationAdelicLattice.theta_norm_summable φ₁ Z₁ z₁) (DerivativeFactorizationAdelicLattice.theta_norm_summable φ₂ Z₂ z₂)]
  rw [← (Equiv.sumArrowEquivProdArrow ι κ ℚ).symm.tsum_eq]
  apply tsum_congr
  intro x
  change (tensorInput φ₁ φ₂).1 (DerivativeFactorizationDefinitions.diagonal (Sum.elim x.1 x.2)) *
      DerivativeFactorizationDefinitions.kernel (fromBlocks Z₁.matrix 0 0 Z₂.matrix) (Sum.elim x.1 x.2)
        (Sum.elim z₁ z₂) = _
  rw [tensorInput_apply, kernel_block]
  change (φ₁.1 (DerivativeFactorizationDefinitions.diagonal x.1) * φ₂.1 (DerivativeFactorizationDefinitions.diagonal x.2)) *
      (DerivativeFactorizationDefinitions.kernel Z₁.matrix x.1 z₁ * DerivativeFactorizationDefinitions.kernel Z₂.matrix x.2 z₂) = _
  ring

theorem direct_sum_factorization
    (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ)
    (Z₁₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Sum ι κ))
    (hZ : Z₁₂.matrix = Matrix.fromBlocks Z₁.matrix 0 0 Z₂.matrix)
    (φ₁ : DerivativeFactorizationDefinitions.Input ι) (φ₂ : DerivativeFactorizationDefinitions.Input κ) :
    ∃ φ₁₂ : DerivativeFactorizationDefinitions.Input (Sum ι κ),
      (∀ a, φ₁₂.1 a = φ₁.1 (fun i => a (Sum.inl i)) *
        φ₂.1 (fun j => a (Sum.inr j))) ∧
      (∀ z₁ z₂, DerivativeFactorizationDefinitions.completed φ₁₂ Z₁₂ (Sum.elim z₁ z₂) =
        DerivativeFactorizationDefinitions.completed φ₁ Z₁ z₁ * DerivativeFactorizationDefinitions.completed φ₂ Z₂ z₂) := by
  refine ⟨tensorInput φ₁ φ₂, tensorInput_apply φ₁ φ₂, ?_⟩
  intro z₁ z₂
  simp only [DerivativeFactorizationDefinitions.completed, AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor, completionForm_block Z₁ Z₂ Z₁₂ hZ,
    Complex.exp_add, hZ, theta_block]
  ring

end

end OAI.RepresentationTheory.Theta.Factorization.Derivative
