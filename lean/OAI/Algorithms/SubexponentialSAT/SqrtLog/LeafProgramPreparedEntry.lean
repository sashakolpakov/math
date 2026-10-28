import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchBlank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchContextBaseInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyPorts

namespace OAI.Algorithms

/-! Actual marked and accepted query staging discharges the residual's
initial blankness requirements. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem entry_ports (i : Fin 768) (hi : i∈entryBlankPorts) :
    ¬Query.Protected i ∧ i≠321 ∧ i≠699 ∧ i≠705 ∧ i≠706 := by
  simp only [entryBlankPorts,List.mem_append,Residual.Native.collectorBlankPorts,
    LeafHighContextProgram.changed,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> decide

theorem marked_initial (a : Factor.Data) (hc : Query.CleanWork a) :
    NodeNative.Blank (Query.markedInput (Query.Carried.reference a)) ∧
    (∀i,i∈entryBlankPorts → (Query.markedInput (Query.Carried.reference a)).stacks i=[]) ∧
    (Query.markedInput (Query.Carried.reference a)).stacks 728=[] ∧
    (∀i,i∈PreparedBranchContext.blankPorts → (Query.markedInput (Query.Carried.reference a)).stacks i=[]) := by
  have hr := Query.Carried.reference_clean a hc
  refine ⟨PreparedNodeReady.marked_blank _ (PreparedNodeReady.cleanWork_blank _ hr),?_,?_,
    PreparedBranchContext.marked_masked_blanks a hc⟩
  · intro i hi
    have hp := entry_ports i hi
    exact (Query.markedInput_frame _ i hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2).trans (hr i hp.1 hp.2.1)
  · exact (Query.markedInput_frame _ 728 (by decide) (by decide) (by decide)).trans
      (hr 728 (by decide) (by decide))

theorem unmarked_initial (a : Factor.Data) (hc : Query.CleanWork a) :
    NodeNative.Blank (Query.unmarkedInput (Query.Carried.reference a)) ∧
    (∀i,i∈entryBlankPorts → (Query.unmarkedInput (Query.Carried.reference a)).stacks i=[]) ∧
    (Query.unmarkedInput (Query.Carried.reference a)).stacks 728=[] ∧
    (∀i,i∈PreparedBranchContext.blankPorts → (Query.unmarkedInput (Query.Carried.reference a)).stacks i=[]) := by
  have hr := Query.Carried.reference_clean a hc
  refine ⟨PreparedNodeReady.unmarked_blank _ (PreparedNodeReady.cleanWork_blank _ hr),?_,?_,
    PreparedBranchContext.unmarked_masked_blanks a hc⟩
  · intro i hi
    have hp := entry_ports i hi
    exact (Query.unmarkedInput_frame _ i hp.2.2.2.1 hp.2.2.2.2).trans (hr i hp.1 hp.2.1)
  · exact (Query.unmarkedInput_frame _ 728 (by decide) (by decide)).trans
      (hr 728 (by decide) (by decide))

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
