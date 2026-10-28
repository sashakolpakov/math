import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ReindexTheta

/-! # Inverse Siegel Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InverseSiegelAction.CM

noncomputable section

/-! ThetaCycle: inversion of the exact rational period and Jacobi substitutions,
proved by cancellation on the actual positive Lagrangian graph. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem rational_inverse_graph_cancellation (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (x : I → ℂ) :
    let W := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z
    let J := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix
    let J' := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ⁻¹).complexify.denominator W.matrix
    Sum.elim (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ⁻¹).transformSiegel W).matrix *ᵥ (J' *ᵥ (J *ᵥ x)))
      (J' *ᵥ (J *ᵥ x)) = Sum.elim (Z.matrix *ᵥ x) x := by
  dsimp only
  have hm : (γ⁻¹.val.map (algebraMap ℚ ℂ)) * (γ.val.map (algebraMap ℚ ℂ)) = 1 := by
    rw [← Matrix.map_mul]
    change ((γ⁻¹ * γ).val.map (algebraMap ℚ ℂ)) = _
    rw [inv_mul_cancel]
    exact map_one ((algebraMap ℚ ℂ).mapMatrix)
  rw [← MovingTotalPeriod.CM.rational_symplectic_graph_substitution γ⁻¹,
    ← MovingTotalPeriod.CM.rational_symplectic_graph_substitution γ, Matrix.mulVec_mulVec, hm, Matrix.one_mulVec]

theorem rational_inverse_denominator_mul (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ⁻¹).complexify.denominator ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).matrix *
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change _ *ᵥ x = (1 : Matrix I I ℂ) *ᵥ x
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  funext i
  exact congrFun (rational_inverse_graph_cancellation γ Z x) (Sum.inr i)

theorem rational_inverse_siegel_action (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ⁻¹).transformSiegel ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) = Z := by
  apply ReindexTheta.CM.siegel_matrix_ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  have h := rational_inverse_graph_cancellation γ Z x
  dsimp only at h
  have hd : (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ⁻¹).complexify.denominator ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).matrix *ᵥ
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, rational_inverse_denominator_mul, Matrix.one_mulVec]
  rw [hd] at h
  funext i
  exact congrFun h (Sum.inl i)

theorem rational_inverse_denominator (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ⁻¹).complexify.denominator ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).matrix =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix)⁻¹ :=
  (Matrix.inv_eq_left_inv (rational_inverse_denominator_mul γ Z)).symm

theorem rational_inverse_jacobi_action (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (z : I → ℂ) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ⁻¹).jacobiChange ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) z =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix).transpose *ᵥ z := by
  rw [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply, rational_inverse_denominator,
    Matrix.nonsing_inv_nonsing_inv _ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).denominator_det_isUnit Z)]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InverseSiegelAction.CM
