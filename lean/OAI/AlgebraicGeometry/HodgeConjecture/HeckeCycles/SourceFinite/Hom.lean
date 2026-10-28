import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GaussianLift
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedPoissonAutomorphy

/-! # Hom -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Hom.CM

noncomputable section

/-! The source finite lifts form a genuine group homomorphism. This is
derived from the constructed real lift and exact adelic factorization. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealLift.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GaussianLift.CM

universe u v w

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {MpR : Type u} {MpF : Type v} {MpA : Type w} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)

theorem finiteLift_one : FiniteLift.CM.finiteLift E L W (1 : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) = 1 := by
  apply W.includeFinite_injective
  have h := Source.RealLift.CM.lift_factorization E L W 1
  rw [Source.GaussianLift.CM.realLift_one, Source.ComplexAction.CM.Symplectic.symplectic_one, map_one, map_one, one_mul] at h
  simpa only [map_one] using h

theorem finiteLift_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    FiniteLift.CM.finiteLift E L W (g * h) =
      FiniteLift.CM.finiteLift E L W g * FiniteLift.CM.finiteLift E L W h := by
  apply W.includeFinite_injective
  apply mul_left_cancel (a := W.includeReal (Source.RealLift.CM.realLift E L W (g * h)))
  rw [Source.RealLift.CM.lift_factorization, Source.GaussianLift.CM.realLift_mul, map_mul, map_mul]
  rw [Source.ComplexAction.CM.Symplectic.symplectic_mul, map_mul, ← Source.RealLift.CM.lift_factorization E L W g, ← Source.RealLift.CM.lift_factorization E L W h]
  exact ((W.commute (Source.RealLift.CM.realLift E L W h) (FiniteLift.CM.finiteLift E L W g)).symm).mul_mul_mul_comm _ _

def finiteHom : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →* MpF where
  toFun := FiniteLift.CM.finiteLift E L W
  map_one' := finiteLift_one E L W
  map_mul' := finiteLift_mul E L W

def finiteAction : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :=
  W.finite.action.comp (finiteHom E L W)

theorem finiteAction_covariance (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
      (finiteAction E L W g φ) (Source.UnitaryEq.CM.Frames.period E g z)).comp (fderiv ℂ (Source.UnitaryEq.CM.Frames.period E g) z) =
      RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ z :=
  FiniteLift.CM.rational_oneForm_covariance E L W hPoissonAutomorphy g φ z hz

theorem canonical_covariance
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
      (finiteAction E L W g φ) (Source.UnitaryEq.CM.Frames.period E g z)).comp (fderiv ℂ (Source.UnitaryEq.CM.Frames.period E g) z) =
      RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ z :=
  finiteAction_covariance E L W EstablishedPoissonAutomorphy.CM.full_input g φ z hz

theorem source_covariance
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (ξ : GeometricSource.CM.BallChart) :
    RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
      (finiteAction E L W g (Theta.Weil.CM.finiteWeilInput φ))
      (Source.UnitaryEq.CM.Frames.period E g z) (fderiv ℂ (Source.UnitaryEq.CM.Frames.period E g) z ξ) = GeometricSource.CM.thetaOneForm E L φ z ξ :=
  FiniteLift.CM.source_oneForm_covariance E L W EstablishedPoissonAutomorphy.CM.full_input g φ z hz ξ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Hom.CM
