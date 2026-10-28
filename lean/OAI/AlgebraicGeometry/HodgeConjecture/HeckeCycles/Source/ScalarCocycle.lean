import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign

/-! # Scalar Cocycle -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarCocycle.CM

noncomputable section

/-! The source's explicit half-frame scalar satisfies the group law.
This is derived from the original line action and its frame, before
using any metaplectic representation. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PrescribedAction OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FormCovariance.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem period_one (z : GeometricSource.CM.BallChart) : UnitaryEq.CM.Frames.period E (1 : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) z = z := by
  change RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm B.b E.val.toRingHom 1 z = z
  rw [map_one]
  rfl

theorem period_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) :
    UnitaryEq.CM.Frames.period E (g * h) z = UnitaryEq.CM.Frames.period E g (UnitaryEq.CM.Frames.period E h z) := by
  change RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm B.b E.val.toRingHom (g * h) z = _
  rw [map_mul]
  rfl

theorem lineScale_one (z : GeometricSource.CM.BallChart) : PeriodDifferential.CM.lineScale E (1 : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) z = 1 := by
  unfold PeriodDifferential.CM.lineScale
  rw [UnitaryEq.CM.PrescribedAction.localAction_one, Module.End.one_apply]
  rfl

theorem lineScale_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    PeriodDifferential.CM.lineScale E (g * h) z = PeriodDifferential.CM.lineScale E g (UnitaryEq.CM.Frames.period E h z) * PeriodDifferential.CM.lineScale E h z := by
  change UnitaryEq.CM.Frames.localAction E (g * h) 1 (GeometricSource.CM.BallDatum.lineVector z) 2 = _
  rw [UnitaryEq.CM.PrescribedAction.localAction_mul, Module.End.mul_apply, PeriodDifferential.CM.line_scale_action E h z hz, map_smul]
  change PeriodDifferential.CM.lineScale E h z * PeriodDifferential.CM.lineScale E g (UnitaryEq.CM.Frames.period E h z) = _
  exact mul_comm _ _

def sourceScalar (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) : ℂ :=
  (L.halfDet (UnitaryEq.CM.Frames.period E g z) : ℂ) / (PeriodDifferential.CM.lineScale E g z * (L.halfDet z : ℂ))

theorem sourceScalar_ne_zero (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) : sourceScalar E L g z ≠ 0 :=
  div_ne_zero (Units.ne_zero _) (mul_ne_zero (PeriodDifferential.CM.lineScale_ne_zero E g z hz) (Units.ne_zero _))

theorem sourceScalar_one (z : GeometricSource.CM.BallChart) : sourceScalar E L (1 : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) z = 1 := by
  simp only [sourceScalar, period_one, lineScale_one, one_mul, div_self (Units.ne_zero _)]

theorem sourceScalar_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    sourceScalar E L (g * h) z = sourceScalar E L g (UnitaryEq.CM.Frames.period E h z) * sourceScalar E L h z := by
  simp only [sourceScalar, period_mul, lineScale_mul E g h z hz]
  field_simp

theorem sourceScalar_eq_signed_halfDet (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    sourceScalar E L g z =
      MultiplierSign.CM.sourceSign E L g * (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z))⁻¹ := by
  rw [← MultiplierSign.CM.multiplier_eq_sign E L g z hz]
  unfold sourceScalar FormCovariance.CM.multiplier
  field_simp [PeriodDifferential.CM.lineScale_ne_zero E g z hz, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarCocycle.CM
