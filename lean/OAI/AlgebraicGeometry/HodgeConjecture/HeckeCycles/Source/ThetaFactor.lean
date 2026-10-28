import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Hom

/-! # Theta Factor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaFactor.CM

noncomputable section

/-! The literal source finite representation transforms the full theta
function by the multiplier of its original line and half-determinant frames. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign.CM

universe u v w

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem scalar (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    MultiplierSign.CM.sourceSign E L g * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z) =
      PeriodDifferential.CM.lineScale E g z * (L.halfDet z : ℂ) / (L.halfDet (UnitaryEq.CM.Frames.period E g z) : ℂ) := by
  have h := MultiplierSign.CM.multiplier_eq_sign E L g z hz
  change (L.halfDet (UnitaryEq.CM.Frames.period E g z) : ℂ) *
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z) /
      (PeriodDifferential.CM.lineScale E g z * (L.halfDet z : ℂ)) = MultiplierSign.CM.sourceSign E L g at h
  have he := (div_eq_iff (mul_ne_zero (PeriodDifferential.CM.lineScale_ne_zero E g z hz) (Units.ne_zero _))).mp h
  apply (eq_div_iff (Units.ne_zero _)).mpr
  calc
    _ = MultiplierSign.CM.sourceSign E L g * ((L.halfDet (UnitaryEq.CM.Frames.period E g z) : ℂ) *
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z)) := by ring
    _ = MultiplierSign.CM.sourceSign E L g * (MultiplierSign.CM.sourceSign E L g * (PeriodDifferential.CM.lineScale E g z * (L.halfDet z : ℂ))) :=
      congrArg (fun a : ℂ => MultiplierSign.CM.sourceSign E L g * a) he
    _ = _ := by rw [← mul_assoc, ← pow_two, MultiplierSign.CM.sourceSign_square, one_mul]

variable {MpR : Type u} {MpF : Type v} {MpA : Type w} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)

theorem theta (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (ξ : GeometricSource.CM.Positions E places → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (SourceFinite.Hom.CM.finiteAction E L W g φ) (L.period (UnitaryEq.CM.Frames.period E g z))
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).jacobiChange (L.period z) ξ) =
      (PeriodDifferential.CM.lineScale E g z * (L.halfDet z : ℂ) / (L.halfDet (UnitaryEq.CM.Frames.period E g z) : ℂ)) *
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z) ξ *
          RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ (L.period z) ξ) := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (W.finite.action (SourceFinite.FiniteLift.CM.finiteLift E L W g) φ) _ _ = _
  rw [SourceFinite.FiniteLift.CM.finiteLift_action, RepresentationTheory.Theta.Geometric.LinearTheta.theta_smul_input]
  have hp := UnitaryEq.CM.PeriodCovariance.period_covariance E L g z hz
  rw [hp, (hPoissonAutomorphy W (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).2.2.2.2, smul_eq_mul,
    ← mul_assoc, scalar E L g z hz]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaFactor.CM
