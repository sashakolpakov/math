import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicFrameDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallConnected
import OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare
import OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

/-! # Source Intrinsic Half Ratio -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicHalfRatio.CM

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
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

def sourceNativeHalfRatio (z : B.Domain) : ℂ :=
  IndexedCovariance.CM.indexedThetaMultiplier (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
    (fun j => (L j).coordinates) hL)
      (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) /
    ((SourceComponents.CM.directSourceComparison K Q hμ hother).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ)))

theorem source_native_half_denominator_ne_zero (z : B.Domain) :
    (SourceComponents.CM.directSourceComparison K Q hμ hother).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ)) ≠ 0 :=
  mul_ne_zero (((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
    (SourceComponents.CM.directSourceFrames K Q)).2.2.2.2.2.1 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).1)
    (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))

theorem source_native_half_ratio_ne_zero (z : B.Domain) :
    sourceNativeHalfRatio K d Q hμ hother L hL z ≠ 0 :=
  div_ne_zero (IndexedCovariance.CM.indexed_theta_multiplier_ne_zero _ _) (source_native_half_denominator_ne_zero K d Q hμ hother L z)

theorem source_native_half_ratio_square (z : B.Domain) :
    sourceNativeHalfRatio K d Q hμ hother L hL z ^ 2 =
      (SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q).det := by
  unfold sourceNativeHalfRatio
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 (source_native_half_denominator_ne_zero K d Q hμ hother L z))).mpr
  exact (SourceIntrinsicFrameDeterminant.CM.source_native_theta_multiplier_square K d Q hμ hother L hL z).trans (mul_comm _ _)

theorem source_native_half_ratio_continuous :
    Continuous (sourceNativeHalfRatio K d Q hμ hother L hL) := by
  have : Nonempty (PeriodTotal.CM.TotalPositions K places) := ⟨.inl (places.distinguished, 0)⟩
  have hZ := MovingTotalPeriod.CM.block_period_holomorphic (fun z => (L 0).period z) (fun z => (L 1).period z)
    (L 0).holomorphic (L 1).holomorphic
  have hm := (IndexedCovariance.CM.indexed_theta_multiplier_holomorphic
    (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother (fun j => (L j).coordinates) hL)
    (fun z => BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z)) hZ).continuousOn
  have hn := (RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.ball_holomorphic_continuous _
    (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
      (SourceComponents.CM.directSourceFrames K Q)).2.2.2.2.1).comp (SourceIntrinsicBall.CM.source_native_ball_continuous K B)
  have hs₀ := (L 0).halfDet_holomorphic.continuousOn.domRestrict
  have hs₁ := (L 1).halfDet_holomorphic.continuousOn.domRestrict
  exact hm.domRestrict.div (hn.mul (hs₀.mul hs₁))
    (source_native_half_denominator_ne_zero K d Q hμ hother L)

theorem source_native_half_ratio_constant (z₀ z : B.Domain) :
    sourceNativeHalfRatio K d Q hμ hother L hL z =
      sourceNativeHalfRatio K d Q hμ hother L hL z₀ := by
  have : ConnectedSpace B.Domain := BallConnected.CM.ball_domain_connected B
  have h := RepresentationTheory.Theta.Adelic.ContinuousSquareRoot.continuous_square_roots_eq (sourceNativeHalfRatio K d Q hμ hother L hL)
    (fun _ => sourceNativeHalfRatio K d Q hμ hother L hL z₀)
    (source_native_half_ratio_continuous K d Q hμ hother L hL) continuous_const
    (source_native_half_ratio_ne_zero K d Q hμ hother L hL)
    (fun y => (source_native_half_ratio_square K d Q hμ hother L hL y).trans
      (source_native_half_ratio_square K d Q hμ hother L hL z₀).symm) z₀ rfl
  exact congrFun h z

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicHalfRatio.CM
