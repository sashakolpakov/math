import OAI.Analysis.HodgeTheory.Integration

/-! # Chart Integration -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ChartIntegration.CM

noncomputable section

/-! ThetaCycle: continuity of genuine chart integrals with fixed subordinate cutoffs. -/

open scoped _root_.Topology
open Set Function Filter _root_.MeasureTheory

open OAI.Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing

variable {P E M F : Type*} [TopologicalSpace P]
  [TopologicalSpace E] [T2Space E]
  [TopologicalSpace M] [CompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The compact support bound is independent of the parameter. This also
controls continuity at the boundary of the chart target. -/
theorem chart_cutoff_joint_continuous (e : OpenPartialHomeomorph M E)
    (ρ : M → ℝ) (hρ : Continuous ρ) (hs : tsupport ρ ⊆ e.source)
    (f : P → E → F) (hf : ContinuousOn f.uncurry (univ ×ˢ e.target)) :
    Continuous (fun p : P × E => Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff e ρ (f p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hy : p.2 ∈ e.target
  · have hρ' : ContinuousOn (fun q : P × E => ρ (e.symm q.2)) (univ ×ˢ e.target) :=
      (hρ.comp_continuousOn e.symm.continuousOn).comp continuous_snd.continuousOn
        (fun _ hq => hq.2)
    have hc := hρ'.smul hf
    have he : (fun q : P × E => Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff e ρ (f q.1) q.2) =ᶠ[𝓝 p]
        (fun q => ρ (e.symm q.2) • f q.1 q.2) := by
      filter_upwards [(e.open_target.preimage continuous_snd).mem_nhds hy] with q hq
      change q.2 ∈ e.target at hq
      simp only [Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff, indicator_of_mem hq]
    exact (hc.continuousAt ((isOpen_univ.prod e.open_target).mem_nhds ⟨trivial, hy⟩)).congr_of_eventuallyEq he
  · have hk := Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.isCompact_chartCutoff_bound e ρ hs
    have hpk : p.2 ∉ e '' tsupport ρ := by
      rintro ⟨x, hx, hxp⟩
      exact hy (hxp ▸ e.map_source (hs hx))
    have he : (fun q : P × E => Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff e ρ (f q.1) q.2) =ᶠ[𝓝 p]
        (fun _ => 0) := by
      filter_upwards [(hk.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds hpk] with q hq
      exact notMem_support.mp (fun h => hq (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.support_chartCutoff_subset e ρ (f q.1) h))
    exact continuousAt_const.congr_of_eventuallyEq he

/-- Integration after a fixed coordinate change is continuous in the family.
The integral is the ordinary Bochner integral, with no supplied continuity
assumption about the integration operator. -/
theorem chart_integral_continuous {V : Type*} [TopologicalSpace V]
    [MeasurableSpace V] [OpensMeasurableSpace V] (μ : Measure V)
    [IsFiniteMeasureOnCompacts μ] (c : V ≃ₜ E)
    (e : OpenPartialHomeomorph M E)
    (ρ : M → ℝ) (hρ : Continuous ρ) (hs : tsupport ρ ⊆ e.source)
    (f : P → E → F) (hf : ContinuousOn f.uncurry (univ ×ˢ e.target)) :
    Continuous (fun p => ∫ y, Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff e ρ (f p) (c y) ∂μ) := by
  have hk := (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.isCompact_chartCutoff_bound e ρ hs).image c.symm.continuous
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support hk
  · exact ((chart_cutoff_joint_continuous e ρ hρ hs f hf).comp
      (continuous_id.prodMap c.continuous)).continuousOn
  · intro p y _ hy
    apply notMem_support.mp
    intro h
    apply hy
    exact ⟨c y, Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.support_chartCutoff_subset e ρ (f p) h, c.symm_apply_apply y⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ChartIntegration.CM
