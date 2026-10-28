import OAI.Analysis.Normed.Function.Holder.C2HolderLattice
import OAI.Analysis.Normed.Function.Holder.Banach.Interpolation

/-! Loss of Hölder exponent preserves the actual periodic forcing. -/
noncomputable section
open Set Module
namespace OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {K : Set E} {α : ℝ} {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}

def LatticeHolderSpace.lowerHalf (hα : 0 ≤ α)
    (f : LatticeHolderSpace (K := K) (α := α) e lat) :
    LatticeHolderSpace (K := K) (α := α/2) e lat :=
  ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.lowerHalf hα f.val, f.property⟩

omit [Fintype ι] in
@[simp] theorem LatticeHolderSpace.value_lowerHalf (hα : 0 ≤ α)
    (f : LatticeHolderSpace (K := K) (α := α) e lat) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (f.lowerHalf hα).val = OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val := rfl

omit [Fintype ι] in
theorem LatticeHolderSpace.norm_lowerHalf_le_twice (hα : 0 ≤ α)
    (f : LatticeHolderSpace (K := K) (α := α) e lat) :
    ‖f.lowerHalf hα‖ ≤ 2*‖f‖ :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.norm_lowerHalf_le_twice hα f.val

end OAI.Analysis.Normed.Function.Holder
