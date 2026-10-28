import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.KernelSumHalfRatio
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicComparison
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Comparison

/-! # Intrinsic Kernel Sum -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSum.CM

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
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q))
  (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
  (hC : ∀ j, (C j).a = Q.a j ∧ (C j).delta = Q.delta)

def sumComparisonFiniteInput (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * 2) :=
  Comparison.CM.comparisonFiniteInput N
    (ReindexTheta.CM.finiteInputReindex (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
      (IndexedCovariance.CM.indexedFiniteOscillatorInput (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN C hC) φ))

end FiniteInput

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
  (hμ : ∀ j, d j (places.representative places.distinguished) = true)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

include hG in
theorem sum_comparison_multiplier_factor (z₀ z : B.Domain) :
    IndexedCovariance.CM.indexedThetaMultiplier (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL)
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) =
      KernelSumHalfRatio.CM.sumComparisonHalfRatio K d Q hμ N hN L hL z₀ *
        (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
          (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ))) := by
  have he := div_mul_cancel₀
    (IndexedCovariance.CM.indexedThetaMultiplier (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL)
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)))
    (KernelSumHalfRatio.CM.sum_comparison_half_denominator_ne_zero K d Q hμ N hG L z)
  exact he.symm.trans (congrArg (fun c : ℂ => c *
    (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ))))
    (KernelSumHalfRatio.CM.sum_comparison_half_ratio_constant K d Q hμ N hN hG L hL z₀ z))

include hG in
theorem sum_comparison_indexed_completed_theta
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z : B.Domain) (ξ : PeriodTotal.CM.TotalPositions K places → ℂ) :
    let γ := IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN (fun j => (L j).coordinates) hL
    let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (IndexedCovariance.CM.indexedFiniteOscillatorInput γ φ) (IntrinsicKernelSumPeriod.CM.sumComparisonIndexedPeriod K d Q hμ N z)
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  exact (congrArg (fun W => RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed
    (IndexedCovariance.CM.indexedFiniteOscillatorInput (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL) φ) W
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL)).jacobiChange
      (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ξ))
    (IntrinsicKernelSumPeriod.CM.sum_comparison_period_transform K d Q hμ N hN hG L hL z)).trans
    (IndexedCovariance.CM.indexed_completed_theta_covariance _ φ _ ξ)

include hG in
theorem sum_comparison_completed_theta
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z : B.Domain) (ξ : PeriodTotal.CM.TotalPositions K places → ℂ) :
    let γ := IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN (fun j => (L j).coordinates) hL
    let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta N
      (sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ)
      (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm i)) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  have hn := Comparison.CM.comparison_input_completed_theta N
    (ReindexTheta.CM.finiteInputReindex (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
      (IndexedCovariance.CM.indexedFiniteOscillatorInput (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
        (fun j => (L j).coordinates) hL) φ))
    (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
    (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL)).jacobiChange
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ξ ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm i))
  have he := SourceIntrinsicComparison.CM.completed_reindex_from_target (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
    (IndexedCovariance.CM.indexedFiniteOscillatorInput (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL) φ)
    (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL)).jacobiChange
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ξ)
  exact hn.trans (he.trans (sum_comparison_indexed_completed_theta K d Q hμ N hN hG L hL φ z ξ))

include hG in
theorem sum_comparison_completed_theta_normalized
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z₀ z : B.Domain) (ξ : PeriodTotal.CM.TotalPositions K places → ℂ) :
    let γ := IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN (fun j => (L j).coordinates) hL
    let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta N
      (sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ)
      (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm i)) =
      KernelSumHalfRatio.CM.sumComparisonHalfRatio K d Q hμ N hN L hL z₀ *
        (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
          (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ))) * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  exact (sum_comparison_completed_theta K d Q hμ N hN hG L hL φ z ξ).trans
    (congrArg (fun c => c * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ
      (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ξ)
      (sum_comparison_multiplier_factor K d Q hμ N hN hG L hL z₀ z))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSum.CM
