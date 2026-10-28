import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Order.Compact

/-! # Proper Map Norm Bound -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ProperMapNormBound.Construction

/-! A continuous norm bound supplied by the target makes a map from a
proper normed space proper. -/

open _root_.Metric Set

theorem isProperMap_of_continuous_norm_bound
    {E Y : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [TopologicalSpace Y] [T2Space Y] [CompactlyCoherentSpace Y]
    (f : E → Y) (hf : Continuous f) (h : Y → ℝ) (hh : Continuous h)
    (hbound : ∀ x, ‖x‖ ≤ h (f x)) : IsProperMap f := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hf, fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := (hK.image hh).bddAbove
  apply (isCompact_closedBall (0 : E) C).of_isClosed_subset (hK.isClosed.preimage hf)
  intro x hx
  change dist x 0 ≤ C
  rw [dist_zero_right]
  exact (hbound x).trans (hC (Set.mem_image_of_mem h hx))

end OAI.NumberTheory.ArithmeticGroups.Lattices.ProperMapNormBound.Construction
