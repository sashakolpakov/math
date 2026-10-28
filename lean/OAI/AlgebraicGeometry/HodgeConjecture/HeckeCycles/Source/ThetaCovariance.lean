import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Projection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PoissonAutomorphy

/-! # Theta Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaCovariance.CM

noncomputable section

/-! PoissonAutomorphy's actual finite transform acts on the canonical first derivative
at the source's actual transformed period. The period identity is proved
from the original prescribed Lagrangian, rather than supplied as input. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PeriodCovariance OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PoissonAutomorphy.CM

universe u v w

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {MpR : Type u} {MpF : Type v} {MpA : Type w} [Group MpR] [Group MpF] [Group MpA]

theorem canonical_first_covariance (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (W.finiteAction (ComplexAction.CM.Symplectic.symplectic E L.coordinates g) φ)
        (L.period (UnitaryEq.CM.Frames.period E g z))).comp
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).jacobiChange (L.period z)) =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z) •
      RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (L.period z) := by
  rw [UnitaryEq.CM.PeriodCovariance.period_covariance E L g z hz]
  exact RepresentationTheory.Theta.Geometric.LinearTheta.canonical_first_covariance W (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)
    (hPoissonAutomorphy W (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).2.2.2.2 φ (L.period z)

theorem source_first_covariance (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (W.finiteAction (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)
        (Theta.Weil.CM.finiteWeilInput φ)) (L.period (UnitaryEq.CM.Frames.period E g z))).comp
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).jacobiChange (L.period z)) =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z) •
      fderiv ℂ (GeometricSource.CM.thetaSeries φ (L.period z)) 0 := by
  rw [Theta.Weil.CM.source_first_is_canonical]
  exact canonical_first_covariance E L hPoissonAutomorphy W g _ z hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaCovariance.CM
