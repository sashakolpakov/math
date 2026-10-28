import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SmoothCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothRepresentativeSupport

/-! # Schwartz Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SchwartzCoordinates

noncomputable section

/-! The original Green solution has actual compact Schwartz representatives of its bounded chart localizations near every point. -/

open _root_.TopologicalSpace _root_.MeasureTheory TemperedDistribution Set Filter
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

theorem holomorphicMetricSmoothGreen_exists_schwartz_coordinates (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    {x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hx : x ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) (hc : h.smoothDolbeaultOneCoercive V) :
    ∃ τ : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), ∃ hτ : HasCompactSupport τ, ∃ hτD : tsupport τ ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i),
      (∀ z, τ z = Complex.ofReal (τ z).re) ∧ τ =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) ∧
      ∃ g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport g ∧ tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) ∧
        (∀ z, g z = Complex.ofReal (g z).re) ∧ g =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) ∧
        ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1, ∃ q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1),
          HasCompactSupport q ∧ tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) ∧ q.toLp 2 volume = ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)))) := by
  let H := SmoothCoordinates.holomorphicMetricSmoothGreen_exists_smooth_coordinates V h e he i hx hc
  let τ := H.choose
  let hτ := H.choose_spec.choose
  let hτD := H.choose_spec.choose_spec.choose
  have hτdata := H.choose_spec.choose_spec.choose_spec
  let g := hτdata.2.2.choose
  have hg := hτdata.2.2.choose_spec
  exact ⟨τ, hτ, hτD, hτdata.1, hτdata.2.1, g, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1,
    fun a =>
      let S := hg.2.2.2.2 a
      let q := Analysis.HodgeTheory.Decomposition.CompactRepresentative.Constructions.vectorSmoothRepresentativeSchwartz g hg.1 (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)))) S.choose S.choose_spec.2 S.choose_spec.1
      let hq := SmoothRepresentativeSupport.vectorSmoothRepresentativeSchwartz_tsupport g hg.1 (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)))) S.choose S.choose_spec.2 S.choose_spec.1
      ⟨q, hg.1.of_isClosed_subset (isClosed_tsupport q) hq, hq.trans hg.2.1,
        Analysis.HodgeTheory.Decomposition.CompactRepresentative.Constructions.vectorSmoothRepresentativeSchwartz_toLp g hg.1 (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)))) S.choose S.choose_spec.2 S.choose_spec.1⟩⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SchwartzCoordinates
