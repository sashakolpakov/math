import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexBare
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Hom

/-! # Weil Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.WeilData.CM

noncomputable section

/-! Constructed Weil data and a genuine finite group action on the original
ball-theta source coordinates. No Weil representation is a source hypothesis. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]

def dimension (places : GeometricSource.CM.Places E) : ℕ := Fintype.card (GeometricSource.CM.Positions E places)

abbrev RealCoverGroup (places : GeometricSource.CM.Places E) := Constructed.ConstructedAdelicGroup.CM.RealGroup (dimension E places)
abbrev FiniteCoverGroup (places : GeometricSource.CM.Places E) := Constructed.ConstructedAdelicGroup.CM.FiniteGroup (dimension E places)
abbrev AdelicCoverGroup (places : GeometricSource.CM.Places E) := Constructed.ConstructedAdelicGroup.CM.AdelicGroup (dimension E places)

def weilData (places : GeometricSource.CM.Places E) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) (RealCoverGroup E places) (FiniteCoverGroup E places) (AdelicCoverGroup E places) :=
  WeilReindexBare.CM.Data.weilData (GeometricSource.CM.Positions E places)

variable {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

def finiteHom : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →* FiniteCoverGroup E places :=
  SourceFinite.Hom.CM.finiteHom E L (weilData E places)

def finiteAction : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :=
  SourceFinite.Hom.CM.finiteAction E L (weilData E places)

theorem canonical_covariance (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
      (finiteAction E L g φ) (UnitaryEq.CM.Frames.period E g z)).comp (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z) =
      RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ z :=
  SourceFinite.Hom.CM.canonical_covariance E L (weilData E places) g φ z hz

theorem source_covariance (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (ξ : GeometricSource.CM.BallChart) :
    RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
      (finiteAction E L g (Theta.Weil.CM.finiteWeilInput φ))
      (UnitaryEq.CM.Frames.period E g z) (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z ξ) = GeometricSource.CM.thetaOneForm E L φ z ξ :=
  SourceFinite.Hom.CM.source_covariance E L (weilData E places) g φ z hz ξ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.WeilData.CM
