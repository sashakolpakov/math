import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallConnected
import OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare
import OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

/-! # Single Comparison Half Ratio -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonHalfRatio.CM

noncomputable section

/-! The source/native half-frame ratio is a single nonzero constant on
 the actual source ball. The constant comes from the fixed frame change,
 with the theta multiplier and the geometric half-frames retained. -/

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
  (j : Fin 2)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (SingleLineComponents.CM.directSingleLineFrames K Q j))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

def singleComparisonHalfRatio (z : B.Domain) : ℂ :=
  IndexedCovariance.CM.indexedThetaMultiplier (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN
    L.coordinates hL)
      (L.period z.val) /
    (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (L.halfDet z.val : ℂ))

include hG in
theorem single_comparison_half_denominator_ne_zero (z : B.Domain) :
    N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (L.halfDet z.val : ℂ) ≠ 0 :=
  mul_ne_zero ((hG.2.2.2.2.2.1 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).1)
    (Units.ne_zero _)

include hG in
theorem single_comparison_half_ratio_ne_zero (z : B.Domain) :
    singleComparisonHalfRatio K d Q hμ j N hN L hL z ≠ 0 :=
  div_ne_zero (IndexedCovariance.CM.indexed_theta_multiplier_ne_zero _ _) (single_comparison_half_denominator_ne_zero K d Q hμ j N hG L z)

include hG in
theorem single_comparison_half_ratio_square (z : B.Domain) :
    singleComparisonHalfRatio K d Q hμ j N hN L hL z ^ 2 =
      (SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j).det := by
  unfold singleComparisonHalfRatio
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 (single_comparison_half_denominator_ne_zero K d Q hμ j N hG L z))).mpr
  exact (SingleComparisonDeterminant.CM.single_comparison_theta_multiplier_square K d Q hμ j N hN hG L hL z).trans (mul_comm _ _)

include hG in
theorem single_comparison_half_ratio_continuous :
    Continuous (singleComparisonHalfRatio K d Q hμ j N hN L hL) := by
  have : Nonempty (HeckeCycles.GeometricSource.CM.Positions K places) := ⟨(places.distinguished, 0)⟩
  have hm := (IndexedCovariance.CM.indexed_theta_multiplier_holomorphic
    (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL)
    L.period L.holomorphic).continuousOn
  have hn := (RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.ball_holomorphic_continuous _
    hG.2.2.2.2.1).comp (SourceIntrinsicBall.CM.source_native_ball_continuous K B)
  have hs := L.halfDet_holomorphic.continuousOn.domRestrict
  exact hm.domRestrict.div (hn.mul hs)
    (single_comparison_half_denominator_ne_zero K d Q hμ j N hG L)

include hG in
theorem single_comparison_half_ratio_constant (z₀ z : B.Domain) :
    singleComparisonHalfRatio K d Q hμ j N hN L hL z =
      singleComparisonHalfRatio K d Q hμ j N hN L hL z₀ := by
  have : ConnectedSpace B.Domain := BallConnected.CM.ball_domain_connected B
  have h := RepresentationTheory.Theta.Adelic.ContinuousSquareRoot.continuous_square_roots_eq (singleComparisonHalfRatio K d Q hμ j N hN L hL)
    (fun _ => singleComparisonHalfRatio K d Q hμ j N hN L hL z₀)
    (single_comparison_half_ratio_continuous K d Q hμ j N hN hG L hL) continuous_const
    (single_comparison_half_ratio_ne_zero K d Q hμ j N hN hG L hL)
    (fun y => (single_comparison_half_ratio_square K d Q hμ j N hN hG L hL y).trans
      (single_comparison_half_ratio_square K d Q hμ j N hN hG L hL z₀).symm) z₀ rfl
  exact congrFun h z

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonHalfRatio.CM
