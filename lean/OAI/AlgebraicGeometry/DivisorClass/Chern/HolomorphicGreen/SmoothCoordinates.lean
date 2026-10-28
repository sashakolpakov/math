import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.NearAllOrders
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.Cutoff
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth

/-! # Smooth Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SmoothCoordinates

noncomputable section

/-! Every chart point has actual smooth bounded coefficient representatives of the original Green solution with original smooth forcing. -/

open _root_.TopologicalSpace _root_.MeasureTheory TemperedDistribution Set Filter
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth.CM.Construction

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

theorem holomorphicMetricSmoothGreen_exists_smooth_coordinates (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    {x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hx : x ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) (hc : h.smoothDolbeaultOneCoercive V) :
    ∃ τ : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), ∃ hτ : HasCompactSupport τ, ∃ hτD : tsupport τ ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i),
      (∀ z, τ z = Complex.ofReal (τ z).re) ∧ τ =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) ∧
      ∃ g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport g ∧ tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) ∧
        (∀ z, g z = Complex.ofReal (g z).re) ∧ g =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) ∧
        ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1, ∃ q : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →ᵇ Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1,
          ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.boundedFunctionDistribution q = (ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)))) : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) ∧
            ContDiff ℝ (⊤ : ℕ∞) (q : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) := by
  let H := NearAllOrders.holomorphicMetricSmoothGreen_exists_local_all_orders V h e he i hx hc
  let τ := H.choose
  let hτ := H.choose_spec.choose
  let hτD := H.choose_spec.choose_spec.choose
  have hτdata := H.choose_spec.choose_spec.choose_spec
  let g := hτdata.2.2.choose
  have hg := hτdata.2.2.choose_spec
  exact ⟨τ, hτ, hτD, hτdata.1, hτdata.2.1, g, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1,
    fun a =>
      let S := ComplexMultiplication.HodgeComparison.Smooth.CM.Construction.sobolev_all_orders_smooth (hg.2.2.2.2 a)
      ⟨S.choose, Eq.trans S.choose_spec.1
        (congrArg (fun v : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) => (v : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)))
          (Cutoff.holomorphicMetricSmoothGreen_cutoff_L2 V h e he i (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) g (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a))),
        S.choose_spec.2⟩⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SmoothCoordinates
