import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineFrameDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallConnected
import OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare
import OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

/-! # Single Line Half Ratio -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineHalfRatio.CM

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
  (j : Fin 2) (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

def singleSourceNativeHalfRatio (z : B.Domain) : ℂ :=
  IndexedCovariance.CM.indexedThetaMultiplier (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j
    L.coordinates hL)
      (L.period z.val) /
    ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (L.halfDet z.val : ℂ))

theorem single_source_native_half_denominator_ne_zero (z : B.Domain) :
    (SingleLineComponents.CM.directSingleLineComparison K Q hμ j).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (L.halfDet z.val : ℂ) ≠ 0 :=
  mul_ne_zero (((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
    (SingleLineComponents.CM.directSingleLineFrames K Q j)).2.2.2.2.2.1 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).1)
    (Units.ne_zero _)

theorem single_source_native_half_ratio_ne_zero (z : B.Domain) :
    singleSourceNativeHalfRatio K d Q hμ j L hL z ≠ 0 :=
  div_ne_zero (IndexedCovariance.CM.indexed_theta_multiplier_ne_zero _ _) (single_source_native_half_denominator_ne_zero K d Q hμ j L z)

theorem single_source_native_half_ratio_square (z : B.Domain) :
    singleSourceNativeHalfRatio K d Q hμ j L hL z ^ 2 =
      (SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j).det := by
  unfold singleSourceNativeHalfRatio
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 (single_source_native_half_denominator_ne_zero K d Q hμ j L z))).mpr
  exact (SingleLineFrameDeterminant.CM.single_source_native_theta_multiplier_square K d Q hμ j L hL z).trans (mul_comm _ _)

theorem single_source_native_half_ratio_continuous :
    Continuous (singleSourceNativeHalfRatio K d Q hμ j L hL) := by
  have : Nonempty (HeckeCycles.GeometricSource.CM.Positions K places) := ⟨(places.distinguished, 0)⟩
  have hm := (IndexedCovariance.CM.indexed_theta_multiplier_holomorphic
    (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL)
    L.period L.holomorphic).continuousOn
  have hn := (RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.ball_holomorphic_continuous _
    (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
      (SingleLineComponents.CM.directSingleLineFrames K Q j)).2.2.2.2.1).comp (SourceIntrinsicBall.CM.source_native_ball_continuous K B)
  have hs := L.halfDet_holomorphic.continuousOn.domRestrict
  exact hm.domRestrict.div (hn.mul hs)
    (single_source_native_half_denominator_ne_zero K d Q hμ j L)

theorem single_source_native_half_ratio_constant (z₀ z : B.Domain) :
    singleSourceNativeHalfRatio K d Q hμ j L hL z =
      singleSourceNativeHalfRatio K d Q hμ j L hL z₀ := by
  have : ConnectedSpace B.Domain := BallConnected.CM.ball_domain_connected B
  have h := RepresentationTheory.Theta.Adelic.ContinuousSquareRoot.continuous_square_roots_eq (singleSourceNativeHalfRatio K d Q hμ j L hL)
    (fun _ => singleSourceNativeHalfRatio K d Q hμ j L hL z₀)
    (single_source_native_half_ratio_continuous K d Q hμ j L hL) continuous_const
    (single_source_native_half_ratio_ne_zero K d Q hμ j L hL)
    (fun y => (single_source_native_half_ratio_square K d Q hμ j L hL y).trans
      (single_source_native_half_ratio_square K d Q hμ j L hL z₀).symm) z₀ rfl
  exact congrFun h z

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineHalfRatio.CM
