import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PrescribedCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Betti

/-! # Metric Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.MetricCurvature

noncomputable section

/-! The original normalized Betti Chern comparison supplies the exact difference needed for an actual metric. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicCurvatureChernScale_ne_zero : Holomorphic.CurvatureD.holomorphicCurvatureChernScale ≠ 0 :=
  inv_ne_zero Complex.two_pi_I_ne_zero

section Exact

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem scaled_deRham_class_difference_exact (F G : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 2) (s : ℂ) (hs : s ≠ 0)
    (he : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 2 (s • F) = Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 2 (s • G)) :
    ∃ a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = F.val - G.val := by
  obtain ⟨a, ha⟩ := (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_eq_iff E M 2 (s • F) (s • G)).mp he
  have hd : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = s • (F.val - G.val) := by
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = s • F.val - s • G.val at ha
    exact ha.trans (smul_sub s F.val G.val).symm
  refine ⟨s⁻¹ • a, ?_⟩
  rw [map_smul, hd, smul_smul, inv_mul_cancel₀ hs, one_smul]

end Exact

def holomorphicRawMetricClosedForm (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 2 := ⟨h.curvature, h.curvature_closed⟩

theorem holomorphicRawMetricClosedForm_normalized (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) :
    Holomorphic.CurvatureD.holomorphicCurvatureChernScale • holomorphicRawMetricClosedForm V h = HolomorphicMetric.Betti.holomorphicMetricClosedForm V h := rfl

theorem exists_holomorphic_metric_of_normalized_betti (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (F : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 2)
    (hF : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 F.val.val)
    (hreal : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm F.val = -F.val)
    (hclass : (V.deRhamBettiIso 2).hom (V.deRhamClass 2 (Holomorphic.CurvatureD.holomorphicCurvatureChernScale • F)) =
      V.rationalCohomologyInclusion 2 (Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u)) :
    ∃ k : HolomorphicMetric.Data.HolomorphicLineMetricData u, k.curvature = F.val := by
  have he0 : V.deRhamClass 2 (Holomorphic.CurvatureD.holomorphicCurvatureChernScale • F) =
      V.deRhamClass 2 (HolomorphicMetric.Betti.holomorphicMetricClosedForm V h) :=
    (V.deRhamBettiIso 2).toLinearEquiv.injective (hclass.trans (HolomorphicMetric.Betti.holomorphicMetric_deRhamBettiClass V h).symm)
  have he : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass V.analyticModel V.analyticSpace 2 (Holomorphic.CurvatureD.holomorphicCurvatureChernScale • F) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass V.analyticModel V.analyticSpace 2
        (Holomorphic.CurvatureD.holomorphicCurvatureChernScale • holomorphicRawMetricClosedForm V h) :=
    he0.trans (congrArg (V.deRhamClass 2) (holomorphicRawMetricClosedForm_normalized V h)).symm
  exact Holomorphic.PrescribedCurvature.exists_holomorphic_metric_with_curvature V h F.val hF hreal
    (scaled_deRham_class_difference_exact F (holomorphicRawMetricClosedForm V h)
      Holomorphic.CurvatureD.holomorphicCurvatureChernScale holomorphicCurvatureChernScale_ne_zero he)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.MetricCurvature
