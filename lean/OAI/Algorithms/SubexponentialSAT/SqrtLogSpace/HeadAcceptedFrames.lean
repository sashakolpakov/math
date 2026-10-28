import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorCommandFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumFrames

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram
open OAI BitProgram StructuredCalls CommandRegisterFrames

private theorem not_mem_union_iff {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} :
    i ∉ left ∪ right ↔ i ∉ left ∧ i ∉ right := by
  simp only [Finset.mem_union, not_or]

/-- The actual accepted path preserves every outer Boolean control register. -/
theorem accepted_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes HeadSumAssembly.accepted :=
  not_mem_union_iff.mpr ⟨HeadSumAssembly.overlay_not_mem_writes i hi,
    not_mem_union_iff.mpr ⟨FactorCommandFrames.assignment_not_mem_writes i hi,
      HeadSumAssembly.accumulate_not_mem_writes i hi⟩⟩

/-- The same static frame holds through every source prefix of the fixed full
head rescan, so tuple controller flags36–39 need no assumed restoration. -/
theorem register_frame {steps : ℕ}
    {a b : Cfg 40 896 (size (HeadSumAssembly.head HeadSumAssembly.accepted) + 1)}
    (ht : Trace program steps a b) (i : Fin 40) (hi : 16 ≤ i.val) :
    b.regs i = a.regs i :=
  HeadSumAssembly.head_register_frame _ i hi (accepted_not_mem_writes i hi) ht

/-- The concrete accepted assignment, including its real table producer,
never writes the pair accumulator. This inspects all called program footprints. -/
theorem accepted_pair_not_mem : (851 : Fin 896) ∉
    CommandStackFrames.writes HeadSumAssembly.accepted :=
  not_mem_union_iff.mpr ⟨HeadSumFrames.overlay_pair_not_mem,
    not_mem_union_iff.mpr ⟨FactorCommandFrames.assignment_not_mem_851,
      HeadSumFrames.accumulate_pair_not_mem⟩⟩

/-- Every source prefix of the fixed whole head program retains the identical
pair word, so its already proved decoded meaning is unchanged. -/
theorem pair_frame {steps : ℕ}
    {a b : Cfg 40 896 (size (HeadSumAssembly.head HeadSumAssembly.accepted) + 1)}
    (ht : Trace program steps a b) : b.stacks 851 = a.stacks 851 :=
  HeadSumFrames.head_pair_prefix _ accepted_pair_not_mem ht

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram
