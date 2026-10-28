import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationMetric
import OAI.RepresentationTheory.Theta.Geometric.QuotientIndexedFrames
import OAI.RepresentationTheory.Theta.Geometric.GaugeOpens

/-! # Metric -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.Metric.Geometric

noncomputable section

/-! The Gaussian metric in the actual algebraic theta quotient frames.
The frame weights are lattice invariant and obey the metric gluing law
for the evaluated native sheaf transition units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) (hP : matrix.transpose = -matrix)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))

def thetaFrameMetricWeight (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) : ℝ :=
  (PolarizationMetric.Geometric.polarizationWeight F) w * ‖RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w‖ ^ 2

theorem thetaFrameMetricWeight_positive
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hw : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) : 0 < (thetaFrameMetricWeight F) hP U V i w :=
  mul_pos (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight_pos F.riemannForm w)
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.1 i.2 w hw.1 hw.2)))

theorem thetaFrameMetricWeight_translates (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (l : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice) (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    (thetaFrameMetricWeight F) hP U V i (w + l.val) = (thetaFrameMetricWeight F) hP U V i w := by
  unfold thetaFrameMetricWeight
  rw [RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_translates U V hdeg, norm_mul, mul_pow]
  calc
    _ = (‖((PolarizationFactor.Geometric.polarizationFactor F) hP).value l w‖ ^ 2 * (PolarizationMetric.Geometric.polarizationWeight F) (w + l.val)) *
        ‖RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w‖ ^ 2 := by ring
    _ = _ := congrArg (fun r : ℝ => r * ‖RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w‖ ^ 2)
      ((PolarizationMetric.Geometric.polarizationFactor_metric F) hP l w)

theorem thetaFrameMetricWeight_ratio
    (i j : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hi : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    ‖RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2 w / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w‖ ^ 2 *
        (thetaFrameMetricWeight F) hP U V i w = (thetaFrameMetricWeight F) hP U V j w := by
  have hq := norm_ne_zero_iff.mpr (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.1 i.2 w hi.1 hi.2)
  unfold thetaFrameMetricWeight
  rw [norm_div, div_pow]
  field_simp

theorem thetaFrameMetricWeight_native_transition {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hf : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension
      (U.projectiveMap (QuotientAddGroup.mk w)))
    (hg : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g p = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension
      (V.projectiveMap (QuotientAddGroup.mk w)))
    (i j : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (W : X.left.Opens)
    (hi : W ≤ RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2)
    (hj : W ≤ RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left j.1 j.2)
    (hp : p.left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W) (hw : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    ‖RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p.left W hp
      (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf W
        (RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.thetaQuotientIndexedFrame f.left g.left i W hi)
        (RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.thetaQuotientIndexedFrame f.left g.left j W hj) : Γ(X.left, W))‖ ^ 2 *
      (thetaFrameMetricWeight F) hP U V i w = (thetaFrameMetricWeight F) hP U V j w := by
  rw [RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.thetaQuotientIndexedFrame_transition_value U V f g p w hf hg i j W hi hj hp]
  exact (thetaFrameMetricWeight_ratio F) hP U V i j w hw

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.Metric.Geometric
