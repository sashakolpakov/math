import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Parameter Exhaustion -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParameterExhaustion.Dolbeault

noncomputable section

/-! Compact exhaustion sets inside an open finite-dimensional parameter
domain, eventually containing a full neighborhood of each parameter. -/

open _root_.TopologicalSpace Set Filter
open scoped _root_.Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

local instance : ProperSpace P := FiniteDimensional.proper ℝ P

local instance (S : Opens P) : LocallyCompactSpace S := S.isOpen.locallyCompactSpace

def openParameterCompact (S : Opens P) (n : ℕ) : Set P :=
  Subtype.val '' (CompactExhaustion.choice S) n

theorem openParameterCompact_isCompact (S : Opens P) (n : ℕ) :
    IsCompact (openParameterCompact S n) :=
  ((CompactExhaustion.choice S).isCompact n).image continuous_subtype_val

theorem openParameterCompact_subset (S : Opens P) (n : ℕ) :
    openParameterCompact S n ⊆ (S : Set P) := by
  rintro p ⟨q, _, rfl⟩
  exact q.property

theorem openParameterCompact_mono (S : Opens P) {m n : ℕ} (h : m ≤ n) :
    openParameterCompact S m ⊆ openParameterCompact S n :=
  image_mono ((CompactExhaustion.choice S).subset h)

theorem exists_openParameterCompact_mem_nhds (S : Opens P) {p : P} (hp : p ∈ S) :
    ∃ n, openParameterCompact S n ∈ 𝓝 p := by
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice S).exists_mem_nhds ⟨p, hp⟩
  exact ⟨n, S.isOpen.isOpenMap_subtype_val.image_mem_nhds hn⟩

theorem exists_openParameterCompact_product_neighborhood (S : Opens P) {q : P × ℂ}
    (hq : q.1 ∈ S) :
    ∃ m : ℕ, q ∈ interior (openParameterCompact S m) ×ˢ Metric.ball 0 (m : ℝ) := by
  obtain ⟨n, hn⟩ := exists_openParameterCompact_mem_nhds S hq
  obtain ⟨r, hr⟩ := exists_nat_gt ‖q.2‖
  refine ⟨max n r, ?_, ?_⟩
  · exact interior_mono (openParameterCompact_mono S (le_max_left n r))
      (mem_interior_iff_mem_nhds.mpr hn)
  · rw [Metric.mem_ball, dist_zero_right]
    exact hr.trans_le (by exact_mod_cast le_max_right n r)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParameterExhaustion.Dolbeault
