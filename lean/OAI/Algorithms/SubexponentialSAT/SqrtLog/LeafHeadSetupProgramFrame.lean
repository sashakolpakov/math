import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStorage

namespace OAI.Algorithms

/-! The isolated bank never enlarges a non-output stack. This includes work
ports and the copy temporary, not only protected source masters. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem returned_nonoutput_eq {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hn : ∀ p∈outs,i≠p.2) :
    (returned reg hs ins outs a b).stacks i=
      if i∈workPorts hs ∨ i=temporary then [] else a.stacks i := by
  by_cases hw : i∈workPorts hs
  · rw [returned,finish_empty _ _ _ _ hw]
    simp [hw]
  have hno : ¬∃j,workPort hs j=i := by
    rintro ⟨j,rfl⟩
    exact hw (work_mem_workPorts hs j)
  have hin : ∀ p∈inputCopies hs ins,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    intro he
    exact hno ⟨q.2,he.symm⟩
  have hout : ∀ p∈outputCopies hs outs,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hn q hq
  calc
    (returned reg hs ins outs a b).stacks i=(prepared hs ins a).stacks i :=
      (finish_frame _ _ _ i hw hout).trans
        (embedState_stack_frame reg (workPort hs) _ b i hno)
    _ = (beforeCopies temporary (workPorts hs) a).stacks i := copyMany_frame _ _ i hin
    _ = _ := by simp [beforeCopies,resetMany_stacks,clearMany_stacks,hw]

theorem returned_nonoutput_length_le {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hn : ∀ p∈outs,i≠p.2) :
    ((returned reg hs ins outs a b).stacks i).length ≤ (a.stacks i).length := by
  rw [returned_nonoutput_eq reg hs ins outs a b i hn]
  split_ifs <;> simp

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
