import OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedOrbitBoundedRepresentatives

/-! # Action Bounds -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ActionBounds.Construction

noncomputable section

/-! A compact family of continuous transformations takes a bounded
subset of a proper normed space into a uniformly bounded subset. -/

open Set

theorem compact_action_bound
    {G V : Type*} [TopologicalSpace G] [NormedAddCommGroup V] [ProperSpace V]
    [SMul G V] [ContinuousSMul G V] (C : Set G) (hC : IsCompact C) (R : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ g ∈ C, ∀ v : V, ‖v‖ ≤ R → ‖g • v‖ ≤ T := by
  have hD := hC.prod (isCompact_closedBall (0 : V) R)
  have hc : Continuous (fun z : G × V => ‖z.1 • z.2‖) :=
    continuous_norm.comp (continuous_fst.smul continuous_snd)
  obtain ⟨T, hT⟩ := hD.bddAbove_image hc.continuousOn
  refine ⟨max 0 T, le_max_left _ _, fun g hg v hv => ?_⟩
  apply le_trans (hT ?_) (le_max_right _ _)
  exact ⟨(g, v), ⟨hg, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv⟩, rfl⟩

theorem compact_orbit_bound
    {G V : Type*} [TopologicalSpace G] [NormedAddCommGroup V]
    [SMul G V] [ContinuousSMul G V] (C : Set G) (hC : IsCompact C) (v : V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g ∈ C, ‖g • v‖ ≤ R := by
  have hc : Continuous (fun g : G => ‖g • v‖) :=
    continuous_norm.comp (continuous_id.smul continuous_const)
  obtain ⟨R, hR⟩ := hC.bddAbove_image hc.continuousOn
  exact ⟨max 0 R, le_max_left _ _, fun g hg =>
    (hR ⟨g, hg, rfl⟩).trans (le_max_right _ _)⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ActionBounds.Construction
