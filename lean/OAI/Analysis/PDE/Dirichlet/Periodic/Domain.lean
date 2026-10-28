import OAI.Analysis.PDE.Dirichlet.SublevelClosure

open Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem neg_of_mem_interior_regular_sublevel {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : E → ℝ}
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0) {x : E}
    (hx : x ∈ interior {y | r y ≤ 0}) : r x < 0 := by
  have hle : r x ≤ 0 := interior_subset (s := {y | r y ≤ 0}) hx
  by_contra hn
  have hz : r x = 0 := le_antisymm hle (le_of_not_gt hn)
  have hmax : IsLocalMax r x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
    simpa only [hz] using hy
  exact hreg x hz hmax.fderiv_eq_zero

theorem interior_regular_sublevel {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : E → ℝ}
    (hr : Continuous r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0) :
    interior {y | r y ≤ 0} = {y | r y < 0} := by
  ext x
  exact ⟨neg_of_mem_interior_regular_sublevel hreg, mem_interior_sublevel_of_neg hr⟩

end OAI.Analysis.PDE.Dirichlet
