import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffUnitSection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RestrictedPairZero
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ForwardChart

/-! # Cutoff Unit Source Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CutoffUnitSourceSupport

noncomputable section

/-! The original Dolbeault source of a cutoff unit frame is supported in an actual compact coordinate set avoiding its unit neighborhood. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicLineCutoffUnitSection_source_support (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Set V.analyticSpace))
    (hse : tsupport f ⊆ e.source) (U : Opens V.analyticSpace)
    (hU : U ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
    (hfone : ∀ y ∈ U, f y = 1) (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hx : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x ∈ U) :
    ∃ K : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V), IsCompact K ∧ K ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧ x ∉ K ∧
      ∀ (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (y : V.analyticSpace), y ∉ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e '' K →
      h.globalFormPair V 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ (Holomorphic.CutoffUnitSection.holomorphicLineCutoffUnitSection V u i f hf hs))
        (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ (Holomorphic.CutoffUnitSection.holomorphicLineCutoffUnitSection V u i f hf hs)) y = 0 := by
  let S := tsupport f \ (U : Set V.analyticSpace)
  have hS : IsCompact S := ((isClosed_tsupport f).inter U.isOpen.isClosed_compl).isCompact
  have hSs : S ⊆ e.source := fun _ hy => hse hy.1
  have hxS : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x ∉ S := fun hy => hy.2 hx
  refine ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' S, Compact.ForwardChart.compact_forward_chart V e hSs hS,
    Compact.ForwardChart.forward_chart_subset_domain V e hSs, Compact.ForwardChart.point_not_in_forward_chart V e hSs x hxS, fun h y hy => ?_⟩
  rw [Compact.ForwardChart.inverse_forward_chart_image V e hSs] at hy
  by_cases hyU : y ∈ U
  · exact h.globalFormPair_zero_of_restrict V 1 _ U
      (Holomorphic.CutoffUnitSection.holomorphicLineCutoffUnitSection_dbar_one V u i f hf hs U hU hfone) y hyU
  · have hyf : y ∉ tsupport f := fun hyf => hy ⟨hyf, hyU⟩
    let W : Opens V.analyticSpace := ⟨(tsupport f)ᶜ, (isClosed_tsupport f).isOpen_compl⟩
    exact h.globalFormPair_zero_of_restrict V 1 _ W
      (Holomorphic.CutoffUnitSection.holomorphicLineCutoffUnitSection_dbar_zero V u i f hf hs W (fun _ hyW => hyW)) y hyf

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CutoffUnitSourceSupport
