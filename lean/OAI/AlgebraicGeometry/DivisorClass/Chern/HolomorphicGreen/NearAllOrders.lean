import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.AllOrders
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.Garding
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.NeighborhoodTest

/-! # Near All Orders -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.NearAllOrders

noncomputable section

/-! Constructed compact localizations of the original smooth-forcing Green solution have every Sobolev order near every chart point. -/

open _root_.TopologicalSpace _root_.MeasureTheory TemperedDistribution Set Filter
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

--
--

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

theorem holomorphicMetricSmoothGreen_exists_local_all_orders (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    {x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hx : x ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) (hc : h.smoothDolbeaultOneCoercive V) :
    ∃ τ : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), ∃ hτ : HasCompactSupport τ, ∃ hτD : tsupport τ ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i),
      (∀ z, τ z = Complex.ofReal (τ z).re) ∧ τ =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) ∧
      ∃ g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport g ∧ tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) ∧
        (∀ z, g z = Complex.ofReal (g z).re) ∧ g =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) ∧
        ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1, ∀ n : ℕ,
          MemSobolev (n : ℝ) 2 ((ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a))))) : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) := by
  let H := h.projectiveLine_exists_sobolev_garding_extension V e he 1 i hx
  let A := H.choose
  have hA := H.choose_spec
  let O := mem_nhds_iff.mp hA.1
  have hO := O.choose_spec
  let C := Compact.NeighborhoodTest.exists_real_schwartz_test_near (hO.2.1.inter (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen)
    (show x ∈ O.choose ∩ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) from ⟨hO.2.2, hx⟩)
  let τ := C.choose
  have hτ := C.choose_spec
  have hτD : tsupport τ ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) := fun z hz => (hτ.2.1 hz).2
  let P := mem_nhds_iff.mp hτ.2.2.2
  have hP := P.choose_spec
  let U := (O.choose ∩ (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _)) ∩ P.choose
  have hU : IsOpen U := (hO.2.1.inter (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen).inter hP.2.1
  have hxU : x ∈ U := ⟨⟨hO.2.2, hx⟩, hP.2.2⟩
  have hUD : U ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) := fun _ hz => hz.1.2
  let R := Compact.NeighborhoodTest.exists_real_coefficient_cutoff hτ.1 (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen hτD
  let η := R.choose
  have hη := R.choose_spec
  let G := Compact.NeighborhoodTest.exists_real_schwartz_test_near hU hxU
  let g := G.choose
  have hg := G.choose_spec
  exact ⟨τ, hτ.1, hτD, hτ.2.2.1, hτ.2.2.2, g, hg.1, hg.2.1.trans hUD, hg.2.2.1, hg.2.2.2,
    fun a => AllOrders.holomorphicMetricSmoothGreen_local_all_orders V h e he i τ hτ.1 hτD hc η hη.1 hη.2.1 hη.2.2.1
      (fun z hz => (hη.2.2.2 z hz).eq_of_nhds) U hU hUD (fun z hz => hP.1 hz.2)
      A (h.projectiveLineSobolevCoefficient V e 1 i x) hA.2.1 hA.2.2.1
      hA.2.2.2.2.1.choose_spec hA.2.2.2.1.choose_spec hA.2.2.2.2.2.choose_spec.1
      hA.2.2.2.2.2.choose_spec.2 (fun z hz => hO.1 hz.1.1) g hg.1 hg.2.2.1 hg.2.1 a⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.NearAllOrders

run_cmd Lean.modifyEnv (fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "holomorphicMetricSmoothGreen_exists_local_all_orders")
