import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InverseSiegelAction
import OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

/-! # Indexed Inverse Multiplier -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedInverseMultiplier.CM

noncomputable section

/-! A rational oscillator followed by its inverse has one constant
nonzero theta multiplier along a connected holomorphic period family.
The identities use the actual constructed finite-input operators. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization
open OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

variable {I : Type} [Fintype I] [DecidableEq I]

def indexedInverseMultiplier (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) : ℂ :=
  IndexedCovariance.CM.indexedThetaMultiplier γ Z *
    IndexedCovariance.CM.indexedThetaMultiplier γ⁻¹ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z)

theorem indexed_inverse_multiplier_ne_zero (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    indexedInverseMultiplier γ Z ≠ 0 :=
  mul_ne_zero (IndexedCovariance.CM.indexed_theta_multiplier_ne_zero _ _) (IndexedCovariance.CM.indexed_theta_multiplier_ne_zero _ _)

theorem indexed_inverse_multiplier_square (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    indexedInverseMultiplier γ Z ^ 2 = 1 := by
  rw [indexedInverseMultiplier, mul_pow, IndexedCovariance.CM.indexed_theta_multiplier_square,
    IndexedCovariance.CM.indexed_theta_multiplier_square, InverseSiegelAction.CM.rational_inverse_denominator,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact mul_inv_cancel₀ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).denominator_det_isUnit Z).ne_zero

theorem indexed_inverse_multiplier_continuous
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Nonempty I]
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) {s : Set V} (Z : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (hZ : DifferentiableOn ℂ (fun x => (Z x).matrix) s) :
    Continuous (fun x : s => indexedInverseMultiplier γ (Z x.val)) := by
  have hW := MovingTotalPeriod.CM.symplectic_period_holomorphic (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z hZ
  exact ((IndexedCovariance.CM.indexed_theta_multiplier_holomorphic γ Z hZ).continuousOn.domRestrict).mul
    ((IndexedCovariance.CM.indexed_theta_multiplier_holomorphic γ⁻¹
      (fun x => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel (Z x)) hW).continuousOn.domRestrict)

theorem indexed_inverse_multiplier_constant
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Nonempty I]
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) {s : Set V} [ConnectedSpace s] (Z : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (hZ : DifferentiableOn ℂ (fun x => (Z x).matrix) s) (x₀ x : s) :
    indexedInverseMultiplier γ (Z x.val) = indexedInverseMultiplier γ (Z x₀.val) := by
  have h := RepresentationTheory.Theta.Adelic.ContinuousSquareRoot.continuous_square_roots_eq (fun x : s => indexedInverseMultiplier γ (Z x.val))
    (fun _ => indexedInverseMultiplier γ (Z x₀.val))
    (indexed_inverse_multiplier_continuous γ Z hZ) continuous_const
    (fun y => indexed_inverse_multiplier_ne_zero γ (Z y.val))
    (fun y => (indexed_inverse_multiplier_square γ (Z y.val)).trans
      (indexed_inverse_multiplier_square γ (Z x₀.val)).symm) x₀ rfl
  exact congrFun h x

theorem rational_jacobi_transpose_cancel (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ξ : I → ℂ) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z
      (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix)ᵀ.mulVec ξ) = ξ := by
  rw [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply, Matrix.mulVec_mulVec,
    ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv _ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).denominator_det_isUnit Z),
    Matrix.transpose_one, Matrix.one_mulVec]

theorem indexed_inverse_oscillator_completed (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Ψ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ξ : I → ℂ) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (IndexedCovariance.CM.indexedFiniteOscillatorInput γ
      (IndexedCovariance.CM.indexedFiniteOscillatorInput γ⁻¹ Ψ)) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ξ =
        indexedInverseMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ξ := by
  have hinv := IndexedCovariance.CM.indexed_completed_theta_covariance γ⁻¹ Ψ
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ξ
  rw [InverseSiegelAction.CM.rational_inverse_siegel_action, InverseSiegelAction.CM.rational_inverse_jacobi_action] at hinv
  have h := IndexedCovariance.CM.indexed_completed_theta_covariance γ (IndexedCovariance.CM.indexedFiniteOscillatorInput γ⁻¹ Ψ) Z
    (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix)ᵀ.mulVec ξ)
  rw [rational_jacobi_transpose_cancel, hinv] at h
  exact h.trans (mul_assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedInverseMultiplier.CM
