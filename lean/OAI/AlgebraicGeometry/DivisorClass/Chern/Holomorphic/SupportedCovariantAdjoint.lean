import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LocalCovariantAdjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SupportedForms
import OAI.Analysis.HodgeTheory.Decomposition.AdjointManifold

/-! # Supported Covariant Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Actual global bundle sections obtained by cutting off the native local covariant adjoint inside a chart and frame. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

def HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantChartAdjoint
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1)) : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n :=
  Holomorphic.SupportedForms.holomorphicLineSupportedExtension u
    (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) n
    (fun x => star (f x)) (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.conjugateFunction_smooth V f hf)
    (by rw [Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.conjugateFunction_tsupport]; exact hs)
    (HolomorphicSmooth.Frames.holomorphicLineSmoothFormOfFrame u i inf_le_right n (h.chartCovariantAdjointOpen V e he i n a))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantChartAdjoint_inFrame
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1))
    (x : (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)) :
    (h.weightedCovariantChartAdjoint V e he i n f hf hs a).val i ⟨x.val, trivial, x.property.2⟩ =
      star (f x.val) • h.chartCovariantAdjointFrame V e i n a x.val := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantChartAdjoint
  rw [Holomorphic.SupportedForms.holomorphicLineSupportedExtension_apply_mem _ _ _ _ _ _ _ i _ x.property,
    HolomorphicSmooth.Frames.holomorphicLineSmoothFormOfFrame_apply,
    Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_self V.analyticModel V.analyticSpace u i x.val x.property.2, one_smul]
  rfl

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantChartAdjoint_zero
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1)) (j : V.analyticSpace)
    (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))
    (hx : x.val ∉ tsupport f) :
    (h.weightedCovariantChartAdjoint V e he i n f hf hs a).val j x = 0 := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantChartAdjoint
  apply Holomorphic.SupportedForms.holomorphicLineSupportedExtension_apply_zero
  rw [Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.conjugateFunction_tsupport]
  exact hx

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
