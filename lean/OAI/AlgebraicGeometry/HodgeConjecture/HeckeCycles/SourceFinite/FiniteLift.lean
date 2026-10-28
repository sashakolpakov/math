import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign

/-! # Finite Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.FiniteLift.CM

noncomputable section

/-! Correct the actual finite metaplectic lift by the sign derived from
the original source frame. This constructs rational theta covariance
for the literal source one-form, with no covariance hypothesis. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FormCovariance.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Projection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PoissonAutomorphy.CM

universe u v w

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {MpR : Type u} {MpF : Type v} {MpA : Type w}
  [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)

def finiteLift (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : MpF :=
  if Source.MultiplierSign.CM.sourceSign E L g = 1 then W.finiteLift (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)
  else W.finite.negOne * W.finiteLift (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)

theorem finiteLift_covers (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    W.finite.project (CM.finiteLift E L W g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g) := by
  unfold CM.finiteLift
  split_ifs
  · exact W.finiteLift_covers _
  · rw [map_mul, W.finite.project_negOne, one_mul, W.finiteLift_covers]

theorem finiteLift_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    W.finite.action (CM.finiteLift E L W g) φ =
      Source.MultiplierSign.CM.sourceSign E L g • W.finiteAction (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g) φ := by
  unfold CM.finiteLift
  split_ifs with h
  · rw [h, one_smul]
    rfl
  · have he := (Source.MultiplierSign.CM.sourceSign_eq_one_or_neg_one E L g).resolve_left h
    rw [map_mul, LinearEquiv.mul_apply, W.finite.genuine, he]
    exact (neg_one_smul ℂ (W.finiteAction (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g) φ)).symm

theorem rational_oneForm_covariance (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0,u,v,w})
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
      (W.finite.action (CM.finiteLift E L W g) φ) (Source.UnitaryEq.CM.Frames.period E g z)).comp
        (fderiv ℂ (Source.UnitaryEq.CM.Frames.period E g) z) =
      RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ z := by
  rw [finiteLift_action, map_smul, Pi.smul_apply, ContinuousLinearMap.smul_comp,
    Source.FormCovariance.CM.oneForm_covariance E L hPoissonAutomorphy W g φ z hz, Source.MultiplierSign.CM.multiplier_eq_sign E L g z hz,
    smul_smul, ← pow_two, Source.MultiplierSign.CM.sourceSign_square, one_smul]

theorem source_oneForm_covariance (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0,u,v,w})
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (ξ : GeometricSource.CM.BallChart) :
    RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
      (W.finite.action (CM.finiteLift E L W g) (Theta.Weil.CM.finiteWeilInput φ))
      (Source.UnitaryEq.CM.Frames.period E g z) (fderiv ℂ (Source.UnitaryEq.CM.Frames.period E g) z ξ) = GeometricSource.CM.thetaOneForm E L φ z ξ := by
  have h := congrArg (fun f : GeometricSource.CM.BallChart →L[ℂ] ℂ => f ξ)
    (rational_oneForm_covariance E L W hPoissonAutomorphy g (Theta.Weil.CM.finiteWeilInput φ) z hz)
  simpa only [ContinuousLinearMap.comp_apply, Theta.Projection.CM.canonical_oneForm_eq_source] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.FiniteLift.CM
