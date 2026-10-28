import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.Basic

noncomputable section
namespace OAI.Geometry.Nikodym

open Set

/-- A continuous curve whose compact parameter interval stays in an open
set stays there on a slightly larger open parameter interval. -/
theorem continuous_interval_open_extension
    {X : Type*} [TopologicalSpace X] {f : ℝ → X} (hf : Continuous f)
    {U : Set X} (hU : IsOpen U) {a b : ℝ} (hab : a ≤ b)
    (hsub : MapsTo f (Icc a b) U) :
    ∃ l r : ℝ, l < a ∧ b < r ∧ MapsTo f (Ioo l r) U := by
  have hopen : IsOpen (f ⁻¹' U) := hU.preimage hf
  obtain ⟨l, u, hlu, hleft⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hopen.mem_nhds (hsub (left_mem_Icc.mpr hab)))
  obtain ⟨v, r, hvr, hright⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hopen.mem_nhds (hsub (right_mem_Icc.mpr hab)))
  refine ⟨l, r, hlu.1, hvr.2, ?_⟩
  intro t ht
  by_cases hta : t < a
  · exact hleft ⟨ht.1, hta.trans hlu.2⟩
  · by_cases hbt : b < t
    · exact hright ⟨hvr.1.trans hbt, ht.2⟩
    · exact hsub ⟨le_of_not_gt hta, le_of_not_gt hbt⟩

/-- A segment contained in an open set admits a longer affine
parameter interval that is still contained in that set. -/
theorem segment_open_parameter_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {a b : E}
    (hseg : segment ℝ a b ⊆ U) :
    ∃ l r : ℝ, l < 0 ∧ 1 < r ∧
      MapsTo (AffineMap.lineMap a b) (Ioo l r) U := by
  apply continuous_interval_open_extension AffineMap.lineMap_continuous hU
    (by norm_num : (0 : ℝ) ≤ 1)
  intro t ht
  exact hseg (lineMap_mem_segment ℝ a b ht)

end OAI.Geometry.Nikodym
