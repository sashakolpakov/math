import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffOne
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalPairCovectorCongruence

/-! # Cutoff Pair Locality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! Original global differential pairings are unchanged wherever the actual source cutoff is locally one. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoff_operators_pair_one_near (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (x : V.analyticSpace)
    (hone : f =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    h.globalFormPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).val
        (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 c).val x =
      h.globalFormPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 c).val x ∧
    h.globalFormPair V 0 (h.degreeCodifferential V 0 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val)
        (h.degreeCodifferential V 0 c.val) x =
      h.globalFormPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 c.val) x := by
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas V.analyticModel x
  let z := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x
  have heq : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z = x := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e x (mem_chart_source V.analyticModel x)
  have hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u x) := by
    refine ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e x (mem_chart_source V.analyticModel x), ?_⟩
    change Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u x
    rw [heq]
    exact (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
  have hi := ((Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_continuousOn V e).continuousAt
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz.1)).tendsto
  have hi' : Tendsto (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e) (𝓝 z) (𝓝 x) := heq ▸ hi
  have hcoord := h.cutoff_operators_covector_one V e he x f hf a hz (hone.comp_tendsto hi')
  have hD := h.globalFormPair_congr_left_of_covector V e he x 2
    (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).val
    (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 c).val hz hcoord.1
  have hS := h.globalFormPair_congr_left_of_covector V e he x 0
    (h.degreeCodifferential V 0 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val)
    (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 c.val) hz hcoord.2
  exact ⟨Eq.mp (congrArg (fun y => h.globalFormPair V 2
      (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).val
      (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 c).val y = h.globalFormPair V 2
        (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 c).val y) heq) hD,
    Eq.mp (congrArg (fun y => h.globalFormPair V 0
      (h.degreeCodifferential V 0 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val)
      (h.degreeCodifferential V 0 c.val) y = h.globalFormPair V 0
        (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 c.val) y) heq) hS⟩

end

/-! An outer cutoff locally equal to one on the inner cutoff support leaves the original global differential test pairings unchanged. -/

open _root_.TopologicalSpace Filter _root_.MeasureTheory
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoff_operators_test_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hone : ∀ x ∈ tsupport g, f =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (x : V.analyticSpace) :
    let C := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c
    h.globalFormPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).val
        (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 C).val x =
      h.globalFormPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 C).val x ∧
    h.globalFormPair V 0 (h.degreeCodifferential V 0 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val)
        (h.degreeCodifferential V 0 C.val) x =
      h.globalFormPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 C.val) x := by
  let C := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c
  by_cases hx : x ∈ tsupport g
  · exact h.cutoff_operators_pair_one_near V f hf a C x (hone x hx)
  · let e := chartAt V.analyticModel x
    have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas V.analyticModel x
    let z := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x
    have heq : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z = x := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e x (mem_chart_source V.analyticModel x)
    have hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u x) := by
      refine ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e x (mem_chart_source V.analyticModel x), ?_⟩
      change Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u x
      rw [heq]
      exact (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
    have hnot : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∉ tsupport g := heq ▸ hx
    have hzero := h.cutoff_operators_covector_zero V e he x g hg c hz hnot
    have hD (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 2) :
        h.globalFormPair V 2 b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 C).val x = 0 := by
      have hp := h.globalFormPair_zero_of_covector V e he x 2 b
        (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 C).val hz hzero.1
      exact Eq.mp (congrArg (fun y => h.globalFormPair V 2 b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 C).val y = 0) heq) hp
    have hS (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
        h.globalFormPair V 0 b (h.degreeCodifferential V 0 C.val) x = 0 := by
      have hp := h.globalFormPair_zero_of_covector V e he x 0 b (h.degreeCodifferential V 0 C.val) hz hzero.2
      exact Eq.mp (congrArg (fun y => h.globalFormPair V 0 b (h.degreeCodifferential V 0 C.val) y = 0) heq) hp
    exact ⟨(hD _).trans (hD _).symm, (hS _).trans (hS _).symm⟩

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoff_operators_test_integral (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hone : ∀ x ∈ tsupport g, f =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    let C := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg c
    h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).val
        (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 C).val =
      h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 C).val ∧
    h.formIntegralPair V 0 (h.degreeCodifferential V 0 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val)
        (h.degreeCodifferential V 0 C.val) =
      h.formIntegralPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 C.val) := by
  constructor
  · exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (h.cutoff_operators_test_pair V f hf g hg hone a c x).1))
  · exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (h.cutoff_operators_test_pair V f hf g hg hone a c x).2))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
