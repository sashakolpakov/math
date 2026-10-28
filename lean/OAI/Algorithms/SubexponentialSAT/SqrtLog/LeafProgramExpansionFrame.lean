import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramExpansionForward

namespace OAI.Algorithms

/-! Exact frame of the paid forward-row expansion. The returned inline row
is the only retained output; source154 is consumed and all private cells
are restored to their empty entry values. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion
open SubexponentialSAT BitProgram StructuredCalls

theorem finished_stacks (a : Data) (rf : Fin 8 → Bool) (word : List Bool)
    (hwork : ∀ i ∈ scratch, a.stacks i = []) :
    (finished a rf word).stacks =
      Function.update (Function.update a.stacks 154 []) 64 word := by
  funext i
  by_cases hin : ∃ j, stackMap j = i
  · obtain ⟨j,rfl⟩ := hin
    rw [show (finished a rf word).stacks (stackMap j) =
        (HashInputProgram.Loop.data rf [] (a.stacks 708) (a.stacks 707)
          (a.stacks 700) (a.stacks 280) word [] [] [] []).stacks j from
      embedState_stack register stackMap a _ stackMap_injective j]
    fin_cases j <;>
      simp_all [HashInputProgram.Loop.data,HashInputProgram.Loop.tapes,stackMap,scratch]
  · have h154 : i ≠ 154 := by intro hi; subst i; exact hin ⟨0,rfl⟩
    have h64 : i ≠ 64 := by intro hi; subst i; exact hin ⟨16,rfl⟩
    rw [finished_frame a rf word i hin]
    simp [h154,h64]

theorem forward_finished_stacks (a : Data) (rf : Fin 8 → Bool) (word : List Bool)
    (hwork : ∀ i ∈ scratch, a.stacks i = []) :
    (finished (reversedInput a) rf word).stacks =
      Function.update (Function.update a.stacks 154 []) 64 word := by
  have hw : ∀ i ∈ scratch, (reversedInput a).stacks i = [] := by
    intro i hi
    have hn : i ≠ 154 := by
      simp only [scratch,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    rw [reversedInput_frame a i hn]
    exact hwork i hi
  rw [finished_stacks _ _ _ hw]
  funext i
  by_cases h64 : i = 64
  · subst i; simp
  by_cases h154 : i = 154
  · subst i; simp
  simp only [Function.update_of_ne h64,Function.update_of_ne h154]
  exact reversedInput_frame a i h154

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
