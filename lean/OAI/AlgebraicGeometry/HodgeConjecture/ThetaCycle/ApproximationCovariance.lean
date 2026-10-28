import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InverseSiegelAction

/-! # Approximation Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ApproximationCovariance.CM

noncomputable section

/-! ThetaCycle: for the actual rational approximating splitting, keep the
original total finite Schwartz input fixed and derive its split-coordinate
theta series and every completed Jacobi coefficient. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)

def approximationSplitFiniteInput (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places)) :
    RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places) :=
  IndexedCovariance.CM.indexedFiniteOscillatorInput (PeriodTotal.CM.approximationSymplecticMatrix K D A)⁻¹ Φ

def approximationThetaMultiplier (z : HeckeCycles.GeometricSource.CM.BallChart) : ℂ :=
  IndexedCovariance.CM.indexedThetaMultiplier (PeriodTotal.CM.approximationSymplecticMatrix K D A)⁻¹ (MovingTotalPeriod.CM.approximationTotalPeriod K D A z)

def approximationJacobiPullback (z : HeckeCycles.GeometricSource.CM.BallChart) :
    (PeriodTotal.CM.TotalPositions K D.places → ℂ) →L[ℂ] (PeriodTotal.CM.TotalPositions K D.places → ℂ) :=
  (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)⁻¹).jacobiChange (MovingTotalPeriod.CM.approximationTotalPeriod K D A z)

theorem approximation_jacobi_pullback_apply (z : HeckeCycles.GeometricSource.CM.BallChart) (u : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    approximationJacobiPullback K D A z u =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator
        (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)).matrix).transpose *ᵥ u :=
  InverseSiegelAction.CM.rational_inverse_jacobi_action _ _ _

theorem approximation_theta_multiplier_ne_zero (z : HeckeCycles.GeometricSource.CM.BallChart) :
    approximationThetaMultiplier K D A z ≠ 0 := IndexedCovariance.CM.indexed_theta_multiplier_ne_zero _ _

theorem approximation_theta_multiplier_square (z : HeckeCycles.GeometricSource.CM.BallChart) :
    approximationThetaMultiplier K D A z ^ 2 =
      (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator
        (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)).matrix).det)⁻¹ := by
  rw [approximationThetaMultiplier, IndexedCovariance.CM.indexed_theta_multiplier_square]
  change ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)⁻¹).complexify.denominator
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).transformSiegel _).matrix).det = _
  rw [InverseSiegelAction.CM.rational_inverse_denominator, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]

theorem approximation_completed_theta_covariance
    (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (u : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed (approximationSplitFiniteInput K D A Φ)
        (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z))
        (approximationJacobiPullback K D A z u) =
      approximationThetaMultiplier K D A z * RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D A z) u := by
  have h := IndexedCovariance.CM.indexed_completed_theta_covariance (PeriodTotal.CM.approximationSymplecticMatrix K D A)⁻¹ Φ
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A z) u
  change RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed _
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)⁻¹).transformSiegel
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).transformSiegel _)) _ = _ at h
  rw [InverseSiegelAction.CM.rational_inverse_siegel_action] at h
  exact h

theorem approximation_completed_jet_covariance
    (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (a : ℕ) (u : Fin a → (PeriodTotal.CM.TotalPositions K D.places → ℂ)) :
    iteratedFDeriv ℂ a (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed (approximationSplitFiniteInput K D A Φ)
        (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z))) 0
        (fun i => approximationJacobiPullback K D A z (u i)) =
      approximationThetaMultiplier K D A z *
        iteratedFDeriv ℂ a (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D A z)) 0 u := by
  have h := IndexedCovariance.CM.indexed_completed_jet_covariance (PeriodTotal.CM.approximationSymplecticMatrix K D A)⁻¹ Φ
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A z) a u
  change iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed _
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)⁻¹).transformSiegel
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).transformSiegel _))) 0 _ = _ at h
  rw [InverseSiegelAction.CM.rational_inverse_siegel_action] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ApproximationCovariance.CM
