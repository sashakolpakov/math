import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyCutoff

/-! # Energy Cutoff Source -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyCutoffSource

noncomputable section

/-! The actual source of energy-cutoff multiplication on a smooth inclusion is the original cut-off antiholomorphic form. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

private theorem holomorphicMetricSmoothEnergyCutoff_source_on_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h
      (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h f hf (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a)) =
      AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a) :=
  (congrArg (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h)
    (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff_on_smooth V h e he i f hf hsf a)).trans
      (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion_source V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a))

def HolomorphicSmoothEnergyCutoffRealPair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (_ : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (_ : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (t : AntiOneSourcePair.HolomorphicAntiOneL2With V h),
    (inner ℂ (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h
      (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h f hf (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a))) t).re =
      (inner ℂ (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)) t).re

theorem holomorphicMetricSmoothEnergyCutoff_re_pair_on_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicSmoothEnergyCutoffRealPair V h := by
  intro e he i f hf hsf a t
  exact
    congrArg (fun w : AntiOneSourcePair.HolomorphicAntiOneL2With V h => (inner ℂ w t).re)
      (holomorphicMetricSmoothEnergyCutoff_source_on_smooth V h e he i f hf hsf a)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyCutoffSource
