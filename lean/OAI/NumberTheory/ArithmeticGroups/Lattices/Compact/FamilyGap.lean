import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantGap

/-! # Family Gap -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.FamilyGap.Construction

noncomputable section

/-! A compact family of continuous functions vanishing at zero gives
a uniform vector gap whenever one value is discrete and nonzero. -/

open scoped _root_.Topology
open Set Filter _root_.Metric

theorem uniform_gap_of_compact_family_discrete_values
    {P E F : Type*} [TopologicalSpace P] [NormedAddCommGroup E]
    [TopologicalSpace F] [Zero F]
    (K : Set P) (hK : IsCompact K) (f : P × E → F) (hf : Continuous f)
    (hf0 : ∀ p ∈ K, f (p, 0) = 0)
    (D : Set F) (hD : IsDiscrete D) (hD0 : (0 : F) ∈ D) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ K, ∀ x, f (p, x) ∈ D → f (p, x) ≠ 0 → ε ≤ ‖x‖ := by
  obtain ⟨U, hU, hUD⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hD 0 hD0
  have hU0 : (0 : F) ∈ U := by
    have h : (0 : F) ∈ U ∩ D := hUD.symm ▸ mem_singleton 0
    exact h.1
  have he : ∀ᶠ x in 𝓝 (0 : E), ∀ p ∈ K, f (p, x) ∈ U := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    have hc : Continuous (fun z : E × P => f (z.2, z.1)) := hf.comp continuous_swap
    exact hc.continuousAt (hU.mem_nhds (by simpa only [hf0 p hp] using hU0))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε, hε, fun p hp x hx hx0 => ?_⟩
  by_contra hle
  have hxball : x ∈ Metric.ball 0 ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using lt_of_not_ge hle
  exact hx0 (mem_singleton_iff.mp (hUD ▸ ⟨hball hxball p hp, hx⟩))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.FamilyGap.Construction
