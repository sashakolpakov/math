import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonHalfRatio
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicComparison
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Comparison

/-! # Single Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparison.CM

noncomputable section

/-! The original finite Schwartz input is transported once through the
fixed rational coordinate change. The resulting native completed theta
series agrees with the original source series throughout the ball, with
its exact constant and geometric half-frame factors. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

section FiniteInput

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (j : Fin 2)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (SingleLineComponents.CM.directSingleLineFrames K Q j))
  (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
  (hC : C.a = Q.a j ∧ C.delta = Q.delta)

def singleComparisonFiniteInput (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * 1) :=
  Comparison.CM.comparisonFiniteInput N
    (ReindexTheta.CM.finiteInputReindex (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
      (IndexedCovariance.CM.indexedFiniteOscillatorInput (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN C hC) φ))

end FiniteInput

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
  (hμ : ∀ j, d j (places.representative places.distinguished) = true)
  (j : Fin 2)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (SingleLineComponents.CM.directSingleLineFrames K Q j))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

include hG in
theorem single_comparison_multiplier_factor (z₀ z : B.Domain) :
    IndexedCovariance.CM.indexedThetaMultiplier (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN
      L.coordinates hL)
        (L.period z.val) =
      SingleComparisonHalfRatio.CM.singleComparisonHalfRatio K d Q hμ j N hN L hL z₀ *
        (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
          (L.halfDet z.val : ℂ)) := by
  have he := div_mul_cancel₀
    (IndexedCovariance.CM.indexedThetaMultiplier (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN
      L.coordinates hL)
        (L.period z.val))
    (SingleComparisonHalfRatio.CM.single_comparison_half_denominator_ne_zero K d Q hμ j N hG L z)
  exact he.symm.trans (congrArg (fun c : ℂ => c *
    (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (L.halfDet z.val : ℂ)))
    (SingleComparisonHalfRatio.CM.single_comparison_half_ratio_constant K d Q hμ j N hN hG L hL z₀ z))

include hG in
theorem single_comparison_indexed_completed_theta
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL
    let Z := L.period z.val
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (IndexedCovariance.CM.indexedFiniteOscillatorInput γ φ) (SingleComparisonPeriod.CM.singleComparisonIndexedPeriod K Q hμ j N z)
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  exact (congrArg (fun W => RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed
    (IndexedCovariance.CM.indexedFiniteOscillatorInput (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN
      L.coordinates hL) φ) W
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN
      L.coordinates hL)).jacobiChange
      (L.period z.val) ξ))
    (SingleComparisonPeriod.CM.single_comparison_period_transform K d Q hμ j N hN hG L hL z)).trans
    (IndexedCovariance.CM.indexed_completed_theta_covariance _ φ _ ξ)

include hG in
theorem single_comparison_completed_theta
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL
    let Z := L.period z.val
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta N
      (singleComparisonFiniteInput K Q hμ j N hN L.coordinates hL φ)
      (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm i)) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  have hn := Comparison.CM.comparison_input_completed_theta N
    (ReindexTheta.CM.finiteInputReindex (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
      (IndexedCovariance.CM.indexedFiniteOscillatorInput (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN
        L.coordinates hL) φ))
    (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
    (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN
      L.coordinates hL)).jacobiChange
        (L.period z.val) ξ ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm i))
  have he := SourceIntrinsicComparison.CM.completed_reindex_from_target (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
    (IndexedCovariance.CM.indexedFiniteOscillatorInput (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN
      L.coordinates hL) φ)
    (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN
      L.coordinates hL)).jacobiChange
        (L.period z.val) ξ)
  exact hn.trans (he.trans (single_comparison_indexed_completed_theta K d Q hμ j N hN hG L hL φ z ξ))

include hG in
theorem single_comparison_completed_theta_normalized
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z₀ z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL
    let Z := L.period z.val
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta N
      (singleComparisonFiniteInput K Q hμ j N hN L.coordinates hL φ)
      (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm i)) =
      SingleComparisonHalfRatio.CM.singleComparisonHalfRatio K d Q hμ j N hN L hL z₀ *
        (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
          (L.halfDet z.val : ℂ)) * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  exact (single_comparison_completed_theta K d Q hμ j N hN hG L hL φ z ξ).trans
    (congrArg (fun c => c * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ
      (L.period z.val) ξ)
      (single_comparison_multiplier_factor K d Q hμ j N hN hG L hL z₀ z))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparison.CM
