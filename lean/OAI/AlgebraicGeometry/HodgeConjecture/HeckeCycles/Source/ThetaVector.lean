import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DerivativeCoordinates

/-! # Theta Vector -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaVector.CM

noncomputable section

/-! The actual first theta derivative, inserted in the source's period
graph, transforms by the original ambient unitary action and PoissonAutomorphy's
constructed determinant scalar. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PeriodCovariance
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Projection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PoissonAutomorphy.CM

universe u v w

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem graph_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : GeometricSource.CM.Positions E places → ℂ) :
    GeometricSource.CM.graphInAmbient E L.coordinates (L.period (UnitaryEq.CM.Frames.period E g z))
      (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).complexify.denominator
        (L.period z).matrix).mulVec x) =
    ComplexAction.CM.ambientOperator E g (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z) x) := by
  apply (ComplexAction.CM.complexFrame E L.coordinates).injective
  rw [UnitaryEq.CM.PeriodCovariance.complexFrame_graph, ← ComplexAction.CM.complex_matrix_frame, UnitaryEq.CM.PeriodCovariance.complexFrame_graph, UnitaryEq.CM.PeriodCovariance.block_graph_action]
  have he := UnitaryEq.CM.PeriodCovariance.transformed_graph E L g z hz x
  change Sum.elim _ _ = Sum.elim _ _
  rw [he]

def thetaVector (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) : GeometricSource.CM.Ambient E :=
  GeometricSource.CM.graphInAmbient E L.coordinates (L.period z) (Theta.Projection.CM.coefficients (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (L.period z)))

variable {MpR : Type u} {MpF : Type v} {MpA : Type w}
  [Group MpR] [Group MpF] [Group MpA]

theorem coefficient_covariance (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    Theta.Projection.CM.coefficients (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (W.finiteAction (ComplexAction.CM.Symplectic.symplectic E L.coordinates g) φ)
      (L.period (UnitaryEq.CM.Frames.period E g z))) =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z) •
      (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).complexify.denominator
        (L.period z).matrix).mulVec (Theta.Projection.CM.coefficients (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (L.period z)))) := by
  apply DerivativeCoordinates.CM.coefficients_of_covariance
    _ _ _ _ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).denominator_det_isUnit (L.period z))
  exact ThetaCovariance.CM.canonical_first_covariance E L hPoissonAutomorphy W g φ z hz

theorem theta_vector_covariance (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    thetaVector E L (W.finiteAction (ComplexAction.CM.Symplectic.symplectic E L.coordinates g) φ) (UnitaryEq.CM.Frames.period E g z) =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z) •
      ComplexAction.CM.ambientOperator E g (thetaVector E L φ z) := by
  unfold thetaVector
  rw [coefficient_covariance E L hPoissonAutomorphy W g φ z hz, map_smul, graph_action E L g z hz]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaVector.CM
