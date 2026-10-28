import OAI.RepresentationTheory.Theta.Geometric.AutomorphyBundleMetric

/-! # Automorphy Frame Derivative -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! In local period coordinates, the actual bundle transition equals
one fixed lattice factor near the chosen lift. -/

open _root_.Topology Filter

variable {Φ : Torus.Data.CM.ProjectivePeriodData} (J : Φ.AutomorphyFactor)

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.transition_lift_eventuallyEq (i j q : Φ.periodTorus)
    (hq : q ∈ (Φ.periodChart i).source ∩ (Φ.periodChart j).source) :
    (fun z : Φ.space => J.transitionFactor i j (QuotientAddGroup.mk z))
      =ᶠ[𝓝 (Φ.periodChart i q)] J.value (Φ.periodChartDifference i j q) := by
  have hmk : (QuotientAddGroup.mk (Φ.periodChart i q) : Φ.periodTorus) = q := by
    rw [← Φ.periodChart_symm i]
    exact (Φ.periodChart i).left_inv hq.1
  have hm : Tendsto (QuotientAddGroup.mk : Φ.space → Φ.periodTorus)
      (𝓝 (Φ.periodChart i q)) (𝓝 q) := by
    have hc : Continuous (QuotientAddGroup.mk : Φ.space → Φ.periodTorus) := QuotientAddGroup.continuous_mk
    simpa only [ContinuousAt, hmk] using (hc.continuousAt (x := Φ.periodChart i q))
  have hδ := (Φ.periodChartDifference_continuousOn i j).continuousAt
    (((Φ.periodChart i).open_source.inter (Φ.periodChart j).open_source).mem_nhds hq)
  have hd : ∀ᶠ z in 𝓝 (Φ.periodChart i q),
      Φ.periodChartDifference i j (QuotientAddGroup.mk z) = Φ.periodChartDifference i j q :=
    hm.eventually (hδ.eventually_mem (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton _)))
  have hi : ∀ᶠ z in 𝓝 (Φ.periodChart i q), Φ.periodChart i (QuotientAddGroup.mk z) = z := by
    filter_upwards [(Φ.periodChart i).open_target.mem_nhds ((Φ.periodChart i).map_source hq.1)] with z hz
    rw [← Φ.periodChart_symm i]
    exact (Φ.periodChart i).right_inv hz
  filter_upwards [hd, hi] with z hz hz'
  simp only [Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.transitionFactor, hz, hz']

end

end OAI.RepresentationTheory.Theta.Geometric
