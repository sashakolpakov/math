import OAI.AlgebraicGeometry.Picard.ThetaConstruction.Metric
import OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

/-! # Connection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.Connection.Geometric

noncomputable section

/-! The connection in each algebraic theta frame is the Gaussian
connection plus the actual logarithmic derivative of its theta gauge.
It is invariant under the original period lattice. -/

open OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet.CM.Torus.AutomorphicTheta

open OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) (hP : matrix.transpose = -matrix)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))

def thetaFrameConnection (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) : ℂ :=
  RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm w v +
    (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w)⁻¹ * fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) w v

theorem thetaGauge_logDerivative_translates (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (l : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice) (w v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hi : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 (w + l.val))⁻¹ *
        fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) (w + l.val) v =
      (((PolarizationFactor.Geometric.polarizationFactor F) hP).value l w)⁻¹ * fderiv ℂ (((PolarizationFactor.Geometric.polarizationFactor F) hP).value l) w v +
        (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w)⁻¹ * fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) w v := by
  have hJ : DifferentiableAt ℂ (((PolarizationFactor.Geometric.polarizationFactor F) hP).value l) w :=
    RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_differentiable (DefinitionsIntegral.Geometric.integralLatticeBasis F) (DefinitionsIntegral.Geometric.integralLatticeForm F)
      (PolarizationFactor.Geometric.latticeEmbedding F) F.riemannForm ((PolarizationFactor.Geometric.integralLatticeEquiv F).symm l) w
  have h := congrArg TrivSqZeroExt.snd
    (RepresentationTheory.Theta.Geometric.GaugeFirstJet.CM.Torus.AutomorphicTheta.consecutiveGauge_firstJet_translates U V hdeg i.1 i.2 l w v hi.1 hJ)
  change fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) (w + l.val) v =
    ((PolarizationFactor.Geometric.polarizationFactor F) hP).value l w * fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) w v +
      fderiv ℂ (((PolarizationFactor.Geometric.polarizationFactor F) hP).value l) w v * RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w at h
  rw [RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_translates U V hdeg, h]
  have hq := RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.1 i.2 w hi.1 hi.2
  have hj := ((PolarizationFactor.Geometric.polarizationFactor F) hP).value_ne_zero l w
  field_simp
  ring

theorem thetaFrameConnection_translates (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (l : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice) (w v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hi : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    (thetaFrameConnection F) hP U V i (w + l.val) v = (thetaFrameConnection F) hP U V i w v := by
  have h := RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection_translation F.riemannForm (DefinitionsIntegral.Geometric.integralLatticeBasis F) (DefinitionsIntegral.Geometric.integralLatticeForm F)
    F.lattice.subtype l w v
  change RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm (w + l.val) v = RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm w v -
    (((PolarizationFactor.Geometric.polarizationFactor F) hP).value l w)⁻¹ * fderiv ℂ (((PolarizationFactor.Geometric.polarizationFactor F) hP).value l) w v at h
  unfold thetaFrameConnection
  rw [h, (thetaGauge_logDerivative_translates F) hP U V hdeg i l w v hi]
  ring

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.Connection.Geometric
