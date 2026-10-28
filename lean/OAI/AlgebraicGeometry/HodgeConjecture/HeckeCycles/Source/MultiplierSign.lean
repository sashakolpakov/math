import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DualAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FormCovariance

/-! # Multiplier Sign -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign.CM.Square

/-! The original source half-determinant and the actual rational
symplectic denominator determine a scalar whose square is one. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DualAction.CM.Frame
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FormCovariance.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaVector.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

def graphFrame (z : GeometricSource.CM.BallChart) : Module.End ℂ (GeometricSource.CM.Positions E places → ℂ) :=
  (GeometricSource.CM.adaptedCoordinates E places d).comp (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z))

theorem graphFrame_intertwines (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (graphFrame E L (UnitaryEq.CM.Frames.period E g z)).comp
      (Matrix.toLin' ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).complexify.denominator
        (L.period z).matrix)) =
      (DualAction.CM.Frame.frameAction E places d g z).comp (graphFrame E L z) := by
  apply LinearMap.ext
  intro x
  change GeometricSource.CM.adaptedCoordinates E places d
    (GeometricSource.CM.graphInAmbient E L.coordinates (L.period (UnitaryEq.CM.Frames.period E g z))
      (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).complexify.denominator (L.period z).matrix).mulVec x)) = _
  rw [ThetaVector.CM.graph_action E L g z hz]
  exact DualAction.CM.Frame.adapted_action E places d g z hz _
    (UnitaryEq.CM.PeriodCovariance.graph_prescribed E L z hz x)

theorem frame_determinant_identity (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (L.halfDet (UnitaryEq.CM.Frames.period E g z) : ℂ) ^ 2 *
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).complexify.denominator (L.period z).matrix).det =
      PeriodDifferential.CM.lineScale E g z ^ 2 * (L.halfDet z : ℂ) ^ 2 := by
  have h := congrArg LinearMap.det (graphFrame_intertwines E L g z hz)
  rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin', DualAction.CM.Frame.frameAction_det] at h
  rw [L.halfDet_square (UnitaryEq.CM.Frames.period E g z) (UnitaryEq.CM.PrescribedAction.period_preserves E g z hz),
    L.halfDet_square z hz]
  exact h

theorem multiplier_square (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) : FormCovariance.CM.multiplier E L g z ^ 2 = 1 := by
  unfold FormCovariance.CM.multiplier
  rw [div_pow, mul_pow, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_sq, frame_determinant_identity E L g z hz, ← mul_pow]
  exact div_self (pow_ne_zero _ (mul_ne_zero (PeriodDifferential.CM.lineScale_ne_zero E g z hz) (Units.ne_zero _)))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign.CM.Square

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign.CM

/-! The source frame multiplier is a single sign for each rational
unitary element. Continuity and connectedness of the actual ball remove
all dependence on the period point. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PrescribedAction OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FormCovariance.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign.CM.Square

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem zero_mem_domain : (0 : GeometricSource.CM.BallChart) ∈ B.domain := by
  change Complex.normSq 0 + Complex.normSq 0 < -(B.b : ℂ).re
  simpa only [Complex.normSq_zero, add_zero] using neg_pos.mpr B.negative

theorem source_halfDet_continuous (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    ContinuousOn (fun z => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z)) B.domain := by
  have h := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDetExtension_continuousOn (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g))).comp
    L.holomorphic.continuousOn (fun z _ => (show (L.period z).matrix ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.siegelSet (GeometricSource.CM.Positions E places) from
      ⟨(L.period z).symmetric, (L.period z).imaginary_posDef⟩))
  apply h.congr
  intro z _
  simp only [Function.comp_apply, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDetExtension, dite_eq_left
    (show (L.period z).matrix ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.siegelSet (GeometricSource.CM.Positions E places) from
      ⟨(L.period z).symmetric, (L.period z).imaginary_posDef⟩)]
  rfl

theorem multiplier_continuous (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    ContinuousOn (FormCovariance.CM.multiplier E L g) B.domain := by
  have hp : ContinuousOn (UnitaryEq.CM.Frames.period E g) B.domain := fun z hz =>
    (PeriodDifferential.CM.period_differentiableAt E g z hz).continuousAt.continuousWithinAt
  have hh := L.halfDet_holomorphic.continuousOn.comp hp (fun z hz => UnitaryEq.CM.PrescribedAction.period_preserves E g z hz)
  have hs : ContinuousOn (PeriodDifferential.CM.lineScale E g) B.domain := fun z _ =>
    (PeriodDifferential.CM.lineScale_differentiableAt E g z).continuousAt.continuousWithinAt
  exact (hh.mul (source_halfDet_continuous E L g)).div
    (hs.mul L.halfDet_holomorphic.continuousOn)
    (fun z hz => mul_ne_zero (PeriodDifferential.CM.lineScale_ne_zero E g z hz) (Units.ne_zero _))

def sourceSign (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : ℂ := FormCovariance.CM.multiplier E L g 0

theorem sourceSign_square (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : sourceSign E L g ^ 2 = 1 :=
  Square.multiplier_square E L g 0 (zero_mem_domain E)

theorem sourceSign_eq_one_or_neg_one (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    sourceSign E L g = 1 ∨ sourceSign E L g = -1 :=
  sq_eq_one_iff.mp (sourceSign_square E L g)

theorem multiplier_eq_sign (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) : FormCovariance.CM.multiplier E L g z = sourceSign E L g := by
  have hc : IsPreconnected B.domain :=
    (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ball_pathConnected (B.b : ℂ) B.negative).isConnected.isPreconnected
  have hsq : Set.EqOn (FormCovariance.CM.multiplier E L g ^ 2) 1 B.domain := fun z hz => Square.multiplier_square E L g z hz
  rcases hc.eq_one_or_eq_neg_one_of_sq_eq (multiplier_continuous E L g) hsq with h | h
  · exact (h hz).trans (h (zero_mem_domain E)).symm
  · exact (h hz).trans (h (zero_mem_domain E)).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign.CM

end

end OAI
