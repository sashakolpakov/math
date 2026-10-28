import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallLineAction
import OAI.RepresentationTheory.Theta.Adelic.GeometricGroup

/-! # Source Intrinsic Ball -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicBall.CM

noncomputable section

/-! The original weighted ball and the native unit ball have explicit
inverse coordinates, using the positive radius of the same coefficient. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K] (B : HeckeCycles.GeometricSource.CM.BallDatum K)

def sourceBallRadius : ℝ := Real.sqrt (-(B.b : ℂ).re)

theorem source_ball_radius_pos : 0 < sourceBallRadius K B :=
  Real.sqrt_pos.mpr (neg_pos.mpr B.negative)

theorem source_ball_radius_sq : sourceBallRadius K B ^ 2 = -(B.b : ℂ).re :=
  Real.sq_sqrt (neg_nonneg.mpr B.negative.le)

def sourceNativeBallPoint (z : B.Domain) : RepresentationTheory.Theta.Adelic.BallNatural.Ball :=
  ⟨fun j => z.val j / (sourceBallRadius K B : ℂ), by
    have hr := source_ball_radius_pos K B
    have hz : Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < -(B.b : ℂ).re := z.property
    change Complex.normSq (z.val 0 / (sourceBallRadius K B : ℂ)) +
      Complex.normSq (z.val 1 / (sourceBallRadius K B : ℂ)) < 1
    rw [Complex.normSq_div, Complex.normSq_div, ← add_div, Complex.normSq_ofReal]
    apply (div_lt_iff₀ (mul_pos hr hr)).mpr
    simpa only [one_mul, ← pow_two, source_ball_radius_sq] using hz⟩

def nativeSourceBallPoint (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) : B.Domain :=
  ⟨fun j => (sourceBallRadius K B : ℂ) * z.val j, by
    have hr := source_ball_radius_pos K B
    have hz := z.property
    have h := mul_lt_mul_of_pos_left hz (mul_pos hr hr)
    change Complex.normSq ((sourceBallRadius K B : ℂ) * z.val 0) +
      Complex.normSq ((sourceBallRadius K B : ℂ) * z.val 1) < -(B.b : ℂ).re
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
    have hs := source_ball_radius_sq K B
    nlinarith⟩

theorem source_native_ball_left_inverse :
    Function.LeftInverse (nativeSourceBallPoint K B) (sourceNativeBallPoint K B) := by
  intro z
  apply Subtype.ext
  funext j
  exact mul_div_cancel₀ (z.val j)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (source_ball_radius_pos K B)))

theorem source_native_ball_right_inverse :
    Function.RightInverse (nativeSourceBallPoint K B) (sourceNativeBallPoint K B) := by
  intro z
  apply Subtype.ext
  funext j
  change (sourceBallRadius K B : ℂ) * z.val j / (sourceBallRadius K B : ℂ) = z.val j
  exact mul_div_cancel_left₀ (z.val j)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (source_ball_radius_pos K B)))

theorem source_native_ball_continuous : Continuous (sourceNativeBallPoint K B) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact ((continuous_apply j).comp continuous_subtype_val).div_const _

theorem native_source_ball_continuous : Continuous (nativeSourceBallPoint K B) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)

def sourceNativeBallHomeomorph : B.Domain ≃ₜ RepresentationTheory.Theta.Adelic.BallNatural.Ball where
  toFun := sourceNativeBallPoint K B
  invFun := nativeSourceBallPoint K B
  left_inv := source_native_ball_left_inverse K B
  right_inv := source_native_ball_right_inverse K B
  continuous_toFun := source_native_ball_continuous K B
  continuous_invFun := native_source_ball_continuous K B

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicBall.CM
