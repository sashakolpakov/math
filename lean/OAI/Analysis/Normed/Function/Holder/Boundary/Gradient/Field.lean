import OAI.Analysis.Normed.Function.Holder.Boundary.Gradient.Periodic
import OAI.Analysis.Normed.Function.Holder.Boundary.Gradient.Lift

noncomputable section
open Set Metric Module
open scoped ContDiff
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance gradientFieldFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gradientFieldFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

theorem exists_uniform_periodic_gradient_field
    (hn : 0 < n) (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : E → ℝ} (hr : ContDiff ℝ ∞ r)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0})
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ U : C2Holder (F := ℝ) hΩK α,
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (C2Holder.value U)) →
      ∃ W : HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α,
        OAI.Analysis.Normed.Function.Holder.HolderMap.value W = C2Holder.firstDerivative U ∧ ‖W‖ ≤ C*‖U‖ := by
  have hKΩ : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
  obtain ⟨C,hC,hbound⟩ := C2Holder.uniform_periodic_gradient_holder_of_local e b hK hr.continuous
    hrp hbounded hΩK hKΩ hα (C2Holder.physical_first_jet_local_holder hn hr hreg hΩK hα1)
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro U hU
  have hholder := hbound ⟨U,hU⟩
  let W := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα.le (C2Holder.firstDerivative U) hholder
  refine ⟨W,rfl,?_⟩
  have hW := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα.le (C2Holder.firstDerivative U)
    (mul_nonneg hC.le (norm_nonneg U)) hholder
  refine hW.trans (max_le ?_ ?_)
  · exact (C2Holder.norm_firstDerivative_le U).trans
      (le_mul_of_one_le_left (norm_nonneg U) (le_max_left _ _))
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg U)

end OAI.Analysis.Normed.Function.Holder.C2Holder
