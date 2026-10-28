import OAI.RepresentationTheory.Weil.Local.BruhatApproximation
import Mathlib.Topology.MetricSpace.Thickening

/-! # Compact Approximation -/

namespace OAI.RepresentationTheory.Weil.Local.CompactApproximation.Construction

noncomputable section

/-! Compact clopen approximations to an arbitrary compact reference set. -/

open Filter
open scoped _root_.Topology Classical

theorem ultrametric_compact_cthickening_open
    {E : Type*} [MetricSpace E] [IsUltrametricDist E]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    IsOpen (Metric.cthickening r K) := by
  rw [hK.cthickening_eq_biUnion_closedBall hr.le]
  exact isOpen_iUnion fun x => isOpen_iUnion fun _ => IsUltrametricDist.isOpen_closedBall x hr.ne'

theorem clopen_indicator_locallyConstant
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsClopen K) :
    IsLocallyConstant (K.indicator (fun _ => (1 : ℂ))) := by
  have h := (LocallyConstant.charFn ℂ hK).isLocallyConstant
  change IsLocallyConstant (K.indicator (1 : E → ℂ)) at h
  convert! h using 1

theorem compact_indicator_locallyConstant_approximation
    {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [ProperSpace E]
    {K : Set E} (hK : IsCompact K) :
    ∃ (L : Set E) (g : ℕ → E → ℂ), IsCompact L ∧ K ⊆ L ∧
      (∀ j, IsLocallyConstant (g j) ∧ tsupport (g j) ⊆ L ∧ ∀ x, ‖g j x‖ ≤ 1) ∧
      ∀ x, Tendsto (fun j => g j x) atTop (𝓝 (K.indicator (fun _ => (1 : ℂ)) x)) := by
  let r : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ j
  have hrpos (j : ℕ) : 0 < r j := pow_pos (by norm_num) _
  have hrle (j : ℕ) : r j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hrlim : Tendsto r atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num) (by norm_num)
  let L := Metric.cthickening 1 K
  let K' : ℕ → Set E := fun j => Metric.cthickening (r j) K
  let g : ℕ → E → ℂ := fun j => (K' j).indicator (fun _ => 1)
  have hopen (j : ℕ) : IsOpen (K' j) := ultrametric_compact_cthickening_open hK (hrpos j)
  have hclosed (j : ℕ) : IsClosed (K' j) := Metric.isClosed_cthickening
  have hKL (j : ℕ) : K' j ⊆ L := Metric.cthickening_mono (hrle j) K
  refine ⟨L, g, hK.cthickening, Metric.self_subset_cthickening K, fun j => ?_, ?_⟩
  · refine ⟨clopen_indicator_locallyConstant ⟨hclosed j, hopen j⟩, ?_, fun x => ?_⟩
    · apply (closure_minimal _ (hclosed j)).trans (hKL j)
      intro x hx
      by_contra hxj
      exact hx (Set.indicator_of_notMem hxj _)
    · by_cases hx : x ∈ K' j <;> simp [g, hx]
  · intro x
    by_cases hx : x ∈ K
    · have heq : ∀ j, g j x = 1 := by
        intro j
        exact Set.indicator_of_mem (Metric.self_subset_cthickening K hx) _
      simp only [heq, Set.indicator_of_mem hx]
      exact tendsto_const_nhds
    · have hxnh : Kᶜ ∈ 𝓝 x := hK.isClosed.isOpen_compl.mem_nhds hx
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hxnh
      have hevent : ∀ᶠ j in atTop, g j x = 0 := by
        filter_upwards [hrlim.eventually_lt_const hε] with j hj
        apply Set.indicator_of_notMem
        intro hxj
        rw [show K' j = Metric.cthickening (r j) K from rfl,
          hK.cthickening_eq_biUnion_closedBall (hrpos j).le] at hxj
        obtain ⟨y, hyK, hxy⟩ := Set.mem_iUnion₂.mp hxj
        have hyball : y ∈ Metric.ball x ε := by
          rw [Metric.mem_ball, dist_comm]
          exact hxy.trans_lt hj
        exact hball hyball hyK
      rw [Set.indicator_of_notMem hx]
      exact tendsto_const_nhds.congr' (hevent.mono (fun _ hj => hj.symm))

end

end OAI.RepresentationTheory.Weil.Local.CompactApproximation.Construction
