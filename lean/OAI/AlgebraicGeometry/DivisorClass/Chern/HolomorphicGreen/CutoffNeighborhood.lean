import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SchwartzCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OuterCutoffNeighborhood
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RealLocalizedRepresentative

/-! # Cutoff Neighborhood -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.CutoffNeighborhood

noncomputable section

/-! Every sufficiently small manifold cutoff of the original Green solution has a genuine smooth bundle representative. -/

open _root_.TopologicalSpace _root_.MeasureTheory Set Filter
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

theorem holomorphicMetricSmoothGreen_frame_cutoff_neighborhood (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (x : V.analyticSpace) (hx : x ∈ e.source)
    (hxi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
    (hc : h.smoothDolbeaultOneCoercive V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    ∃ U : Set V.analyticSpace, IsOpen U ∧ x ∈ U ∧
      ∀ ρ : V.analyticSpace → ℝ, ∀ hρ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ ρ,
        tsupport ρ ⊆ U → ∃ b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1,
          Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b = Holomorphic.MultiplierReal.holomorphicMetricRealL2Multiplier V h 1 ρ hρ ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a))) := by
  have hxD : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) := by
    refine ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e x hx, ?_⟩
    change Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x) ∈
      Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
    rw [Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e x hx]
    exact hxi
  let H := SchwartzCoordinates.holomorphicMetricSmoothGreen_exists_schwartz_coordinates V h e he i hxD hc
  let τ := H.choose
  let hτ := H.choose_spec.choose
  let hτD := H.choose_spec.choose_spec.choose
  have hτdata := H.choose_spec.choose_spec.choose_spec
  let g := hτdata.2.2.choose
  have hg := hτdata.2.2.choose_spec
  let Q := hg.2.2.2.2 a
  have houter := Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_near_of_coordinate_support V u e he i τ hτ hτD x hx
    (subset_tsupport τ (ne_of_eq_of_ne hτdata.2.1.eq_of_nhds one_ne_zero))
  have hforward : ContinuousAt (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e) x :=
    (((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous.comp_continuousOn e.continuousOn).continuousAt
      (e.open_source.mem_nhds hx))
  have hgnear : ∀ᶠ y in 𝓝 x, g (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y) = 1 :=
    hg.2.2.2.1.comp_tendsto hforward
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ e.source ∧
      y ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ∧
      (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) y = 1 ∧ g (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y) = 1 := by
    filter_upwards [e.open_source.mem_nhds hx,
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i).isOpen.mem_nhds hxi,
      houter, hgnear] with y hy hi ho hg'
    exact ⟨hy, hi, ho, hg'⟩
  let O := mem_nhds_iff.mp hnear
  have hO := O.choose_spec
  exact ⟨O.choose, hO.2.1, hO.2.2, fun ρ hρ hρU =>
    Holomorphic.RealLocalizedRepresentative.holomorphicMetric_smooth_real_localized_representative V h e he i 1 ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)))
      (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) g Q.choose Q.choose_spec.2.2 ρ hρ
      (fun y hy => ⟨(hO.1 (hρU hy)).1, (hO.1 (hρU hy)).2.1⟩)
      (fun y hy => (hO.1 (hρU hy)).2.2.1) (fun y hy => (hO.1 (hρU hy)).2.2.2)⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.CutoffNeighborhood
