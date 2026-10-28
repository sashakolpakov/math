import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizationFactor
import OAI.RepresentationTheory.Theta.Geometric.PolarizationAutomorphy
import OAI.RepresentationTheory.Theta.Geometric.AutomorphyBundleMetric
import OAI.RepresentationTheory.Theta.Geometric.AutomorphyFrameDerivative
import OAI.RepresentationTheory.Theta.Geometric.PolarizationConnection

/-! # Polarization Metric -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The original reference polarization bundle has its actual positive
Gaussian metric and compatible local connection in the period charts. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)

def Fiber.ReferenceAnalyticFiber.polarizationWeight : F.periodData.space → ℝ := RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight F.form

theorem Fiber.ReferenceAnalyticFiber.polarizationFactor_metric (l : F.periodData.periodIntegerLattice) (w : F.periodData.space) :
    ‖(F.polarizationFactor hP).value l w‖ ^ 2 * F.polarizationWeight (w + l.val) =
      F.polarizationWeight w := by
  have h := RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight_translation (P.referenceBasis hP) P.integralForm
    F.latticeEmbedding F.form F.hermitian (F.integralLatticeEquiv.symm l) w
  rw [F.latticeEmbedding_symm l] at h
  exact h

def Fiber.ReferenceAnalyticFiber.polarizationNormSq : Bundle.TotalSpace ℂ (F.polarizationBundle hP).Fiber → ℝ :=
  (F.polarizationFactor hP).bundleNormSq F.polarizationWeight

theorem Fiber.ReferenceAnalyticFiber.polarizationNormSq_nonneg (p : Bundle.TotalSpace ℂ (F.polarizationBundle hP).Fiber) :
    0 ≤ F.polarizationNormSq hP p :=
  (F.polarizationFactor hP).bundleNormSq_nonneg _ (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight_pos F.form) p

theorem Fiber.ReferenceAnalyticFiber.polarizationNormSq_eq_zero_iff (p : Bundle.TotalSpace ℂ (F.polarizationBundle hP).Fiber) :
    F.polarizationNormSq hP p = 0 ↔ p.snd = 0 :=
  (F.polarizationFactor hP).bundleNormSq_eq_zero_iff _ (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight_pos F.form) p

theorem Fiber.ReferenceAnalyticFiber.polarizationNormSq_continuous : Continuous (F.polarizationNormSq hP) :=
  (F.polarizationFactor hP).bundleNormSq_continuous _ (F.polarizationFactor_metric hP)
    (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationMetricWeight_continuous F.form)

theorem Fiber.ReferenceAnalyticFiber.polarizationConnection_change_frame (i j q : F.periodData.periodTorus)
    (hq : q ∈ (F.periodData.periodChart i).source ∩ (F.periodData.periodChart j).source)
    (v : F.periodData.space) :
    RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.form (F.periodData.periodChart j q) v =
      RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.form (F.periodData.periodChart i q) v -
        ((F.polarizationFactor hP).transitionFactor i j q)⁻¹ *
          fderiv ℂ (fun w : F.periodData.space =>
            (F.polarizationFactor hP).transitionFactor i j (QuotientAddGroup.mk w))
            (F.periodData.periodChart i q) v := by
  let l := F.periodData.periodChartDifference i j q
  rw [((F.polarizationFactor hP).transition_lift_eventuallyEq i j q hq).fderiv_eq]
  have h := RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection_translation F.form (P.referenceBasis hP) P.integralForm
    F.latticeEmbedding (F.integralLatticeEquiv.symm l) (F.periodData.periodChart i q) v
  rw [F.latticeEmbedding_symm l] at h
  have hshift : F.periodData.periodChart i q + l.val = F.periodData.periodChart j q := by
    rw [F.periodData.periodChartDifference_val i j q hq]
    abel
  exact (congrArg (fun w : F.periodData.space => RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.form w v) hshift).symm.trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
