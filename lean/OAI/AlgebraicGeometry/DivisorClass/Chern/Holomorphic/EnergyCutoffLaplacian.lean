import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyCutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffPairLocality
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeakLaplacian

/-! # Energy Cutoff Laplacian -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyCutoffLaplacian

noncomputable section

/-! Actual cutoff multiplication preserves the native weak Laplacian test equation when the outer cutoff is one near the inner test support. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

private theorem holomorphicMetricCutoff_laplacian_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hone : ∀ x ∈ tsupport g, f =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    inner ℂ (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a))
      (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c))) =
    inner ℂ (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)
      (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c))) := by
  let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
  let C := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c
  have hA := h.smoothAntiLaplacianOne_hilbert_pair V A C
  have hB := h.smoothAntiLaplacianOne_hilbert_pair V a C
  have hp := h.cutoff_operators_test_integral V f hf g hg hone a c
  have hD := (IntegralPairZero.holomorphicFormL2WithInclusion_inner V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val
    (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 C).val).trans
      (hp.1.trans (IntegralPairZero.holomorphicFormL2WithInclusion_inner V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val
        (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 C).val).symm)
  have hS := (IntegralPairZero.holomorphicFormL2WithInclusion_inner V h 0 (h.degreeCodifferential V 0 A.val)
    (h.degreeCodifferential V 0 C.val)).trans
      (hp.2.trans (IntegralPairZero.holomorphicFormL2WithInclusion_inner V h 0 (h.degreeCodifferential V 0 a.val)
        (h.degreeCodifferential V 0 C.val)).symm)
  exact hA.trans ((congrArg₂ (fun x y : ℂ => x + y) hD hS).trans hB.symm)

private theorem holomorphicMetricSmoothEnergyCutoff_laplacian_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hone : ∀ x ∈ tsupport g, f =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (v : EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h) :
    inner ℂ (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h f hf v))
      (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c))) =
    inner ℂ (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v)
      (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c))) := by
  let S := EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h
  let M := EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h f hf
  let t := AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c))
  have hleft : Continuous (fun w : EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h => inner ℂ (S (M w)) t) :=
    (S.continuous.comp M.continuous).inner continuous_const
  have hright : Continuous (fun w : EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h => inner ℂ (S w) t) :=
    S.continuous.inner continuous_const
  refine (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion_dense V h).induction_on v (isClosed_eq hleft hright) ?_
  intro a
  have hcut := EnergyCutoff.holomorphicMetricSmoothEnergyCutoff_on_smooth V h e he i f hf hsf a
  have hsrc := (congrArg S hcut).trans
    (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion_source V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a))
  have hp := holomorphicMetricCutoff_laplacian_pair V h f hf g hg hone a c
  have hr := EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion_source V h a
  exact (congrArg (fun w => inner ℂ w t) hsrc).trans
    (hp.trans (congrArg (fun w => inner ℂ w t) hr).symm)

def HolomorphicSmoothGreenCutoffLaplacianTest (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (_ : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (_ : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (_ : ∀ x ∈ tsupport g, f =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (_ : h.smoothDolbeaultOneCoercive V) (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (v : AntiOneSourcePair.HolomorphicAntiOneL2With V h),
    inner ℂ (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h
      (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h f hf (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h v)))
      (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c))) =
    inner ℂ v (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c))

theorem holomorphicMetricSmoothGreenCutoff_laplacian_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicSmoothGreenCutoffLaplacianTest V h := by
  intro e he i f hf hsf g hg hone hc c v
  exact
    (holomorphicMetricSmoothEnergyCutoff_laplacian_test V h e he i f hf hsf g hg hone c
      (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h v)).trans
        (WeakLaplacian.holomorphicMetricSmoothGreen_laplacian_test V h hc v (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyCutoffLaplacian
