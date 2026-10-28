import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallConnected
import OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare
import OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

/-! # Kernel Sum Half Ratio -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.KernelSumHalfRatio.CM

noncomputable section

/-! The source/native half-frame ratio is a single nonzero constant on
 the actual source ball. The constant comes from the fixed frame change,
 with the theta multiplier and both geometric half-frames retained. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

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

def sumComparisonHalfRatio (z : B.Domain) : ℂ :=
  IndexedCovariance.CM.indexedThetaMultiplier (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
    (fun j => (L j).coordinates) hL)
      (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) /
    (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ)))

include hG in
theorem sum_comparison_half_denominator_ne_zero (z : B.Domain) :
    N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ)) ≠ 0 :=
  mul_ne_zero ((hG.2.2.2.2.2.1 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).1)
    (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))

include hG in
theorem sum_comparison_half_ratio_ne_zero (z : B.Domain) :
    sumComparisonHalfRatio K d Q hμ N hN L hL z ≠ 0 :=
  div_ne_zero (IndexedCovariance.CM.indexed_theta_multiplier_ne_zero _ _) (sum_comparison_half_denominator_ne_zero K d Q hμ N hG L z)

include hG in
theorem sum_comparison_half_ratio_square (z : B.Domain) :
    sumComparisonHalfRatio K d Q hμ N hN L hL z ^ 2 =
      (SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q).det := by
  unfold sumComparisonHalfRatio
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 (sum_comparison_half_denominator_ne_zero K d Q hμ N hG L z))).mpr
  exact (IntrinsicKernelSumDeterminant.CM.sum_comparison_theta_multiplier_square K d Q hμ N hN hG L hL z).trans (mul_comm _ _)

include hG in
theorem sum_comparison_half_ratio_continuous :
    Continuous (sumComparisonHalfRatio K d Q hμ N hN L hL) := by
  have : Nonempty (PeriodTotal.CM.TotalPositions K places) := ⟨.inl (places.distinguished, 0)⟩
  have hZ := MovingTotalPeriod.CM.block_period_holomorphic (fun z => (L 0).period z) (fun z => (L 1).period z)
    (L 0).holomorphic (L 1).holomorphic
  have hm := (IndexedCovariance.CM.indexed_theta_multiplier_holomorphic
    (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN (fun j => (L j).coordinates) hL)
    (fun z => BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z)) hZ).continuousOn
  have hn := (RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.ball_holomorphic_continuous _
    hG.2.2.2.2.1).comp (SourceIntrinsicBall.CM.source_native_ball_continuous K B)
  have hs₀ := (L 0).halfDet_holomorphic.continuousOn.domRestrict
  have hs₁ := (L 1).halfDet_holomorphic.continuousOn.domRestrict
  exact hm.domRestrict.div (hn.mul (hs₀.mul hs₁))
    (sum_comparison_half_denominator_ne_zero K d Q hμ N hG L)

include hG in
theorem sum_comparison_half_ratio_constant (z₀ z : B.Domain) :
    sumComparisonHalfRatio K d Q hμ N hN L hL z =
      sumComparisonHalfRatio K d Q hμ N hN L hL z₀ := by
  have : ConnectedSpace B.Domain := BallConnected.CM.ball_domain_connected B
  have h := RepresentationTheory.Theta.Adelic.ContinuousSquareRoot.continuous_square_roots_eq (sumComparisonHalfRatio K d Q hμ N hN L hL)
    (fun _ => sumComparisonHalfRatio K d Q hμ N hN L hL z₀)
    (sum_comparison_half_ratio_continuous K d Q hμ N hN hG L hL) continuous_const
    (sum_comparison_half_ratio_ne_zero K d Q hμ N hN hG L hL)
    (fun y => (sum_comparison_half_ratio_square K d Q hμ N hN hG L hL y).trans
      (sum_comparison_half_ratio_square K d Q hμ N hN hG L hL z₀).symm) z₀ rfl
  exact congrFun h z

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.KernelSumHalfRatio.CM
