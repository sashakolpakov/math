import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartFrameCutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.ChartField

/-! # Nested Frame Cutoff -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.NestedFrameCutoff

noncomputable section

/-! Every actual compact frame cutoff admits a real outer frame cutoff equal to one on a global neighborhood of its support. -/

open _root_.TopologicalSpace Filter Set
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem exists_real_outer_holomorphic_frame_cutoff (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : V.analyticSpace → ℂ)
    (hsg : tsupport g ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)) :
    ∃ f : V.analyticSpace → ℂ, ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f ∧
      tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace) ∧
      (∀ x, f x = Complex.ofReal (f x).re) ∧
      ∀ x ∈ tsupport g, f =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
  have hK := Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.chartCoordinateForward_compact V e (isClosed_tsupport g).isCompact (fun _ hx => (hsg hx).1)
  have hKD := HolomorphicCompact.ChartField.holomorphicLineCutoff_image_domain V e i g hsg
  have H := ChartFrameCutoff.exists_real_holomorphic_chart_frame_cutoff_near V u e he i hK hKD
  let f := H.choose
  have hf := H.choose_spec.1
  have hsf := H.choose_spec.2.1
  have hreal := H.choose_spec.2.2.1
  have hone := H.choose_spec.2.2.2
  refine ⟨f, hf, hsf, hreal, fun x hx => ?_⟩
  have hxsource : x ∈ e.source := (hsg hx).1
  have hcont : ContinuousAt (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e) x :=
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous.continuousAt.comp
      (e.continuousOn.continuousAt (e.open_source.mem_nhds hxsource))
  have hc := (hone (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x) ⟨x, hx, rfl⟩).comp_tendsto hcont.tendsto
  have hlocal : (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y))) =ᶠ[𝓝 x] f :=
    Filter.Eventually.mono (e.open_source.mem_nhds hxsource)
      (fun y hy => congrArg f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e y hy))
  exact hlocal.symm.trans hc

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.NestedFrameCutoff
