import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationFactor
import OAI.RepresentationTheory.Theta.Geometric.PolarizationAutomorphy
import OAI.RepresentationTheory.Theta.Geometric.AutomorphyBundleMetric
import OAI.RepresentationTheory.Theta.Geometric.AutomorphyFrameDerivative
import OAI.RepresentationTheory.Theta.Geometric.PolarizationConnection

/-! # Polarization Metric -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationMetric.Geometric

noncomputable section

/-! The original reference polarization bundle has its actual positive
Gaussian metric and compatible local connection in the period charts. -/

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) (hP : matrix.transpose = -matrix)

def polarizationWeight : (ProjectivePeriodData.Geometric.projectivePeriodData F).space → ℝ := RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight F.riemannForm

theorem polarizationFactor_metric (l : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice) (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    ‖((PolarizationFactor.Geometric.polarizationFactor F) hP).value l w‖ ^ 2 * (polarizationWeight F) (w + l.val) =
      (polarizationWeight F) w := by
  have h := RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight_translation (DefinitionsIntegral.Geometric.integralLatticeBasis F) (DefinitionsIntegral.Geometric.integralLatticeForm F)
    (PolarizationFactor.Geometric.latticeEmbedding F) F.riemannForm F.hermitian ((PolarizationFactor.Geometric.integralLatticeEquiv F).symm l) w
  rw [(PolarizationFactor.Geometric.latticeEmbedding_symm F) l] at h
  exact h

def polarizationNormSq : Bundle.TotalSpace ℂ ((PolarizationFactor.Geometric.polarizationBundle F) hP).Fiber → ℝ :=
  ((PolarizationFactor.Geometric.polarizationFactor F) hP).bundleNormSq (polarizationWeight F)

theorem polarizationNormSq_nonneg (p : Bundle.TotalSpace ℂ ((PolarizationFactor.Geometric.polarizationBundle F) hP).Fiber) :
    0 ≤ (polarizationNormSq F) hP p :=
  ((PolarizationFactor.Geometric.polarizationFactor F) hP).bundleNormSq_nonneg _ (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight_pos F.riemannForm) p

theorem polarizationNormSq_eq_zero_iff (p : Bundle.TotalSpace ℂ ((PolarizationFactor.Geometric.polarizationBundle F) hP).Fiber) :
    (polarizationNormSq F) hP p = 0 ↔ p.snd = 0 :=
  ((PolarizationFactor.Geometric.polarizationFactor F) hP).bundleNormSq_eq_zero_iff _ (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight_pos F.riemannForm) p

theorem polarizationNormSq_continuous : Continuous ((polarizationNormSq F) hP) :=
  ((PolarizationFactor.Geometric.polarizationFactor F) hP).bundleNormSq_continuous _ ((polarizationFactor_metric F) hP)
    (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight_continuous F.riemannForm)

theorem polarizationConnection_change_frame (i j q : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus)
    (hq : q ∈ ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart i).source ∩ ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart j).source)
    (v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart j q) v =
      RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart i q) v -
        (((PolarizationFactor.Geometric.polarizationFactor F) hP).transitionFactor i j q)⁻¹ *
          fderiv ℂ (fun w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space =>
            ((PolarizationFactor.Geometric.polarizationFactor F) hP).transitionFactor i j (QuotientAddGroup.mk w))
            ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart i q) v := by
  let l := (ProjectivePeriodData.Geometric.projectivePeriodData F).periodChartDifference i j q
  rw [(((PolarizationFactor.Geometric.polarizationFactor F) hP).transition_lift_eventuallyEq i j q hq).fderiv_eq]
  have h := RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection_translation F.riemannForm (DefinitionsIntegral.Geometric.integralLatticeBasis F) (DefinitionsIntegral.Geometric.integralLatticeForm F)
    (PolarizationFactor.Geometric.latticeEmbedding F) ((PolarizationFactor.Geometric.integralLatticeEquiv F).symm l) ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart i q) v
  change RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart i q + l.val) v =
    RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart i q) v -
      ((PolarizationFactor.Geometric.polarizationFactor F hP).value l ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart i q))⁻¹ *
        fderiv ℂ ((PolarizationFactor.Geometric.polarizationFactor F hP).value l) ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart i q) v at h
  have hshift : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart i q + l.val = (ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart j q := by
    rw [(ProjectivePeriodData.Geometric.projectivePeriodData F).periodChartDifference_val i j q hq]
    abel
  exact (congrArg (fun w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space => RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm w v) hshift).symm.trans h

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationMetric.Geometric
