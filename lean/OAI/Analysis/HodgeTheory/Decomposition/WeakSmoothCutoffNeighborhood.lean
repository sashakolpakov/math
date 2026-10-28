import OAI.Analysis.HodgeTheory.Decomposition.WeakSmoothNeighborhood
import OAI.Analysis.HodgeTheory.Decomposition.CompactRepresentative
import OAI.Analysis.HodgeTheory.Decomposition.SmoothLocalizedRepresentative

/-! # Weak Smooth Cutoff Neighborhood -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeakSmoothCutoffNeighborhood.Constructions

noncomputable section

/-! Around each point, every subordinate smooth real cutoff of an actual
weak Hodge solution with smooth forcing has a global smooth representative. -/

open _root_.MeasureTheory Set Filter
open scoped SchwartzMap _root_.Manifold ContDiff _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem exists_projective_weak_smooth_cutoff_neighborhood
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n)
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hsol : WeakEquation.Constructions.IsProjectiveWeakHodgeSolution V n u (Form.Constructions.smoothToProjectiveL2 V (n + 1) f))
    (x : V.analyticSpace) :
    ∃ U : Set V.analyticSpace, IsOpen U ∧ x ∈ U ∧
      ∀ ρ : V.analyticSpace → ℝ, ∀ hρ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ ρ,
        tsupport ρ ⊆ U → ∃ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1),
          Form.Constructions.smoothToProjectiveL2 V (n + 1) a =
            SmoothGlobal.Constructions.projectiveRealL2Multiplier V (n + 1) ρ hρ (EnergyDomain.Constructions.projectiveEnergyInclusion V n u) := by
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas _ _
  have hx : x ∈ e.source := mem_chart_source _ _
  obtain ⟨χ, hχ, hχs, hχnear, g, hgc, _hgs, _hgreal, hgnear, v, hv, hvs⟩ :=
    WeakSmoothNeighborhood.Constructions.exists_projective_weak_smooth_neighborhood V e he n u f hsol x hx
  have hforward : ContinuousAt (MeasureVolume.Constructions.chartCoordinateForward V e) x :=
    (((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous.comp_continuousOn
      e.continuousOn).continuousAt (e.open_source.mem_nhds hx))
  have hgnear' : ∀ᶠ y in 𝓝 x, g (MeasureVolume.Constructions.chartCoordinateForward V e y) = 1 :=
    hgnear.comp_tendsto hforward
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ e.source ∧ χ y = 1 ∧ g (MeasureVolume.Constructions.chartCoordinateForward V e y) = 1 := by
    filter_upwards [e.open_source.mem_nhds hx, hχnear, hgnear'] with y hys hyχ hyg
    exact ⟨hys, hyχ, hyg⟩
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
  let c := CompactRepresentative.Constructions.vectorSmoothRepresentativeSchwartz g hgc
    (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he (n + 1) χ hχ hχs (EnergyDomain.Constructions.projectiveEnergyInclusion V n u)) v hvs hv
  have hc : c.toLp 2 volume = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g
      (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he (n + 1) χ hχ hχs (EnergyDomain.Constructions.projectiveEnergyInclusion V n u)) :=
    CompactRepresentative.Constructions.vectorSmoothRepresentativeSchwartz_toLp g hgc _ v hvs hv
  refine ⟨U, hU, hxU, fun ρ hρ hρU => ?_⟩
  exact SmoothLocalizedRepresentative.Constructions.exists_projective_smooth_localized_representative V e he (n + 1)
    (EnergyDomain.Constructions.projectiveEnergyInclusion V n u) χ hχ hχs g c hc ρ hρ
    (fun _ hy => (hUsub (hρU hy)).1)
    (fun _ hy => (hUsub (hρU hy)).2.1)
    (fun _ hy => (hUsub (hρU hy)).2.2)

end

end OAI.Analysis.HodgeTheory.Decomposition.WeakSmoothCutoffNeighborhood.Constructions
