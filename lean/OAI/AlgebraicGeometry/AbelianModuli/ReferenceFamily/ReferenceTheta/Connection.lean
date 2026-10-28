import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.Metric
import OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

/-! # Connection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The connection in each algebraic theta frame is the Gaussian
connection plus the actual logarithmic derivative of its theta gauge.
It is invariant under the original period lattice. -/

open OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet.CM.Torus.AutomorphicTheta

open OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))

def Reference.Fiber.ReferenceAnalyticFiber.thetaFrameConnection (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w v : F.periodData.space) : ℂ :=
  RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.form w v +
    (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w)⁻¹ * fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) w v

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaGauge_logDerivative_translates (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (l : F.periodData.periodIntegerLattice) (w v : F.periodData.space)
    (hi : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 (w + l.val))⁻¹ *
        fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) (w + l.val) v =
      ((F.polarizationFactor hP).value l w)⁻¹ * fderiv ℂ ((F.polarizationFactor hP).value l) w v +
        (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w)⁻¹ * fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) w v := by
  have hJ : DifferentiableAt ℂ ((F.polarizationFactor hP).value l) w :=
    RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_differentiable (P.referenceBasis hP) P.integralForm
      F.latticeEmbedding F.form (F.integralLatticeEquiv.symm l) w
  have h := congrArg TrivSqZeroExt.snd
    (RepresentationTheory.Theta.Geometric.GaugeFirstJet.CM.Torus.AutomorphicTheta.consecutiveGauge_firstJet_translates U V hdeg i.1 i.2 l w v hi.1 hJ)
  change fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) (w + l.val) v =
    (F.polarizationFactor hP).value l w * fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) w v +
      fderiv ℂ ((F.polarizationFactor hP).value l) w v * RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w at h
  rw [RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_translates U V hdeg, h]
  have hq := RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.1 i.2 w hi.1 hi.2
  have hj := (F.polarizationFactor hP).value_ne_zero l w
  field_simp
  ring

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaFrameConnection_translates (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (l : F.periodData.periodIntegerLattice) (w v : F.periodData.space)
    (hi : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    F.thetaFrameConnection hP U V i (w + l.val) v = F.thetaFrameConnection hP U V i w v := by
  have h := RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection_translation F.form (P.referenceBasis hP) P.integralForm
    F.latticeEmbedding (F.integralLatticeEquiv.symm l) w v
  rw [F.latticeEmbedding_symm l] at h
  change RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.form (w + l.val) v = RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.form w v -
    ((F.polarizationFactor hP).value l w)⁻¹ * fderiv ℂ ((F.polarizationFactor hP).value l) w v at h
  unfold Reference.Fiber.ReferenceAnalyticFiber.thetaFrameConnection
  rw [h, F.thetaGauge_logDerivative_translates hP U V hdeg i l w v hi]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
