import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ClassicalCovariance
import OAI.RepresentationTheory.Theta.Kernel.Factorization

/-! # Normalized Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.NormalizedCovariance.CM

noncomputable section

/-! ThetaCycle: absorb the single residual unit scalar into the finite input.
The resulting multiplier squares to the actual Siegel denominator, with
one transformed finite input valid for every positive period. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.Kernel.Factorization OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

theorem exists_rational_gaussian_square_scalar (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N),
      RationalGaussianCovariance.CM.rationalGaussianCoefficient N γ Z ^ 2 * ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix).det = u ^ 2 := by
  obtain ⟨u, hu, h⟩ := RealGaussianCoefficient.CM.real_oscillator_gaussian_coefficient (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) γ)
    (RationalGaussianCovariance.CM.classicalRationalRealOscillator N γ Rat.infinitePlace)
    (RationalGaussianCovariance.CM.classical_rational_real_oscillator_projection N γ Rat.infinitePlace)
  exact ⟨u, hu, fun Z => (h Z).1⟩

def rationalOscillatorUnitScalar (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) : ℂ :=
  (exists_rational_gaussian_square_scalar N γ).choose

theorem rational_oscillator_unit_scalar_ne_zero (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) :
    rationalOscillatorUnitScalar N γ ≠ 0 := by
  have h := (exists_rational_gaussian_square_scalar N γ).choose_spec.1
  intro hzero
  change ‖rationalOscillatorUnitScalar N γ‖ = 1 at h
  rw [hzero, norm_zero] at h
  exact zero_ne_one h

def rationalThetaMultiplier (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) : ℂ :=
  rationalOscillatorUnitScalar N γ / RationalGaussianCovariance.CM.rationalGaussianCoefficient N γ Z

theorem rational_theta_multiplier_square (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    rationalThetaMultiplier N γ Z ^ 2 = ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix).det := by
  have h := (exists_rational_gaussian_square_scalar N γ).choose_spec.2 Z
  change RationalGaussianCovariance.CM.rationalGaussianCoefficient N γ Z ^ 2 * _ = rationalOscillatorUnitScalar N γ ^ 2 at h
  rw [rationalThetaMultiplier, div_pow, ← h]
  exact mul_div_cancel_left₀ _ (pow_ne_zero 2 (RationalGaussianCovariance.CM.rational_gaussian_coefficient_ne_zero N γ Z))

def normalizedFiniteOscillatorInput (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N) :=
  RepresentationTheory.Theta.Kernel.Factorization.scaleInput (rationalOscillatorUnitScalar N γ) (ClassicalCovariance.CM.classicalFiniteOscillatorInput N γ φ)

theorem theta_scale_finite_input {I : Type*} [Fintype I] (c : ℂ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I)
    (B : Matrix I I ℂ) (z : I → ℂ) : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta (RepresentationTheory.Theta.Kernel.Factorization.scaleInput c φ) B z = c * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta φ B z := by
  unfold RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta RepresentationTheory.Theta.Kernel.Factorization.scaleInput
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  exact mul_assoc _ _ _

theorem completed_scale_finite_input {I : Type*} [Fintype I] (c : ℂ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (z : I → ℂ) : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (RepresentationTheory.Theta.Kernel.Factorization.scaleInput c φ) Z z = c * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z z := by
  rw [RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed, theta_scale_finite_input, RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed]
  ring

theorem normalized_completed_theta_covariance (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (normalizedFiniteOscillatorInput N γ φ) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z)
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) = rationalThetaMultiplier N γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z z := by
  rw [normalizedFiniteOscillatorInput, completed_scale_finite_input, rationalThetaMultiplier]
  calc
    _ = (rationalOscillatorUnitScalar N γ / RationalGaussianCovariance.CM.rationalGaussianCoefficient N γ Z) *
        (RationalGaussianCovariance.CM.rationalGaussianCoefficient N γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (ClassicalCovariance.CM.classicalFiniteOscillatorInput N γ φ)
          ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z)) := by
      field_simp [RationalGaussianCovariance.CM.rational_gaussian_coefficient_ne_zero N γ Z]
    _ = _ := by rw [ClassicalCovariance.CM.completed_theta_oscillator_covariance]

theorem normalized_classical_theta_covariance (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta (normalizedFiniteOscillatorInput N γ φ) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).matrix
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) =
      rationalThetaMultiplier N γ Z * ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).thetaCorrectionForm Z) z *
        RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta φ Z.matrix z := by
  have h := normalized_completed_theta_covariance N γ φ Z z
  unfold RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed at h
  apply mul_left_cancel₀ (Complex.exp_ne_zero
    (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).completionForm ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z)
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z)))
  change ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).completionForm
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) * _ = _
  rw [h]
  have he : ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).completionForm
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) * ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).thetaCorrectionForm Z) z =
        ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z := by
    rw [ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor, ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor, ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor, ← Complex.exp_add,
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).completion_correction_identity Z z]
  rw [← he]
  unfold ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.NormalizedCovariance.CM
