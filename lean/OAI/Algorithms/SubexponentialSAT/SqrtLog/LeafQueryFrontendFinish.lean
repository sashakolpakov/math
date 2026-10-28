import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendNumerics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendState

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem lowMask_eval (a : Data) (descending : List Bool)
    (h338 : a.stacks 338=descending) (h134 : a.stacks 134=[])
    (h668 : a.stacks 668=[]) (ht : a.stacks 679=[]) :
    ∃ b, Eval lowMask (12*descending.length+8) a b ∧
      b.stacks 134=descending.reverse.map Bool.not ∧ b.stacks 668=[] ∧
      (∀ i, i≠134 → i≠668 → b.stacks i=a.stacks i) ∧ b.regs 8=a.regs 8 := by
  have hc := copy_eval a 338 668 ⟨by decide,by decide,by decide,ht⟩
  let c := copied a 338 668
  have hp : projectState r2 lowPorts c=HeadIdentifierProgram.LowMask.state (c.regs ∘ r2) descending [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [lowPorts,c,copied_stack,h338,h134,h668]
  obtain ⟨rf,he⟩ := HeadIdentifierProgram.LowMask.trace (c.regs ∘ r2) descending []
  rw [←hp] at he
  let small := HeadIdentifierProgram.LowMask.state rf [] ((descending.map Bool.not).reverse)
  let b := embedState r2 lowPorts c small
  have hl := eval_call_from_state HeadIdentifierProgram.LowMask.program r2 lowPorts c
    (registers_injective ..) lowPorts_injective he
  have hf (i : Fin 768) (hi : i≠134) (hj : i≠668) : b.stacks i=a.stacks i := by
    have h := embedState_stack_frame r2 lowPorts c small i (by
      rintro ⟨j,hj'⟩; fin_cases j <;> simp [lowPorts] at hj' <;> simp_all)
    exact h.trans (by simp [c,copied_stack,hj])
  refine ⟨b,?_,?_,?_,hf,?_⟩
  · simpa [b,small,lowMask,lowCall,h338,show 7*descending.length+5+(5*descending.length+3)=12*descending.length+8 by omega] using hc.seq hl
  · have h := embedState_stack r2 lowPorts c small lowPorts_injective 1
    simpa [b,small,lowPorts,HeadIdentifierProgram.LowMask.state,List.map_reverse] using h
  · exact embedState_stack r2 lowPorts c small lowPorts_injective 0
  · have h := embedState_register_frame r2 lowPorts c small 8 (by decide)
    simpa [b,c,copied,SubexpScanPrimitives.afterCopy,readRegs] using h

theorem offset_eval (a : Data) (he : emptyRange a 650 668) (ho : a.stacks 141=[]) :
    ∃ n ≤ LayoutOffsetProgram.budget (a.stacks 725) (a.stacks 720) (a.stacks 727), ∃ b,
      Eval offsetCall n a b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*BinaryArithmetic.toNat (a.stacks 725)*
        (8*BinaryArithmetic.toNat (a.stacks 720))^(2*BinaryArithmetic.toNat (a.stacks 727)) ∧
      (b.stacks 141).length ≤ LayoutOffsetProgram.outputLength (a.stacks 725) (a.stacks 720) (a.stacks 727) ∧
      (∀ i : Fin 768, i≠141 → b.stacks i=a.stacks i) ∧ b.regs 8=a.regs 8 := by
  have hz650 := he 650 (by decide) (by decide)
  have hz651 := he 651 (by decide) (by decide)
  have hz652 := he 652 (by decide) (by decide)
  have hz653 := he 653 (by decide) (by decide)
  have hz654 := he 654 (by decide) (by decide)
  have hz655 := he 655 (by decide) (by decide)
  have hz656 := he 656 (by decide) (by decide)
  have hz657 := he 657 (by decide) (by decide)
  have hz658 := he 658 (by decide) (by decide)
  have hz659 := he 659 (by decide) (by decide)
  have hz660 := he 660 (by decide) (by decide)
  have hz661 := he 661 (by decide) (by decide)
  have hz662 := he 662 (by decide) (by decide)
  have hz663 := he 663 (by decide) (by decide)
  have hz664 := he 664 (by decide) (by decide)
  have hz665 := he 665 (by decide) (by decide)
  have hz666 := he 666 (by decide) (by decide)
  have hz667 := he 667 (by decide) (by decide)
  have hp : projectState r8 offsetPorts a=LayoutOffsetProgram.input (a.regs ∘ r8)
      (a.stacks 725) (a.stacks 720) (a.stacks 727) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [offsetPorts,
          LayoutOffsetProgram.initial,SubexpBlockParameterProgram.inputWords,ho,hz650,hz651,hz652,hz653,hz654,hz655,hz656,hz657,hz658,hz659,hz660,hz661,hz662,hz663,hz664,hz665,hz666,hz667]
  obtain ⟨n,hn,word,hex,hval,hlen⟩ := offsetCall_eval a (a.stacks 725) (a.stacks 720) (a.stacks 727) hp
  let small := LayoutOffsetProgram.result (a.stacks 725) (a.stacks 720) (a.stacks 727) word
  let b := embedState r8 offsetPorts a small
  have h141 : b.stacks 141=word := embedState_stack r8 offsetPorts a small offsetPorts_injective 9
  refine ⟨n,hn,b,hex,by simpa [h141] using hval,by simpa [h141] using hlen,?_,?_⟩
  · intro i hi
    by_cases him : ∃ j, offsetPorts j=i
    · obtain ⟨j,rfl⟩ := him
      have hj := embedState_stack r8 offsetPorts a small offsetPorts_injective j
      rw [hj]
      fin_cases j <;> simp_all [small,offsetPorts,LayoutOffsetProgram.result,LayoutOffsetProgram.bank,
        LayoutOffsetProgram.initial,SubexpBlockParameterProgram.inputWords,SubexpBlockParameterProgram.state]
    · exact embedState_stack_frame r8 offsetPorts a small i him
  · exact embedState_register_frame r8 offsetPorts a small 8 (by decide)

def cleanupPorts : List (Fin 768) := (List.finRange 262).map (block 417 262 (by decide))
def cleaned (a : Data) : Data := ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks cleanupPorts a.stacks⟩
def cleanupCost (a : Data) := 2*(cleanupPorts.map (fun i => (a.stacks i).length)).sum+789

theorem cleanup_eval (a : Data) (ht : a.stacks 679=[]) :
    Eval clearPrivate (cleanupCost a) a (cleaned a) := by
  have h := BankRoutines.clear_eval (679 : Fin 768) (0 : Fin 40) 1 cleanupPorts
    (List.nodup_finRange 262 |>.map (block_injective ..)) a.regs a.stacks ht
  simpa [clearPrivate,cleanupPorts,cleanupCost,cleaned] using h

theorem cleanup_mem (i : Fin 768) : i ∈ cleanupPorts ↔ 417 ≤ i.val ∧ i.val < 679 := by
  simp only [cleanupPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,rfl⟩; dsimp [block]; omega
  · intro h; exact ⟨⟨i.val-417,by omega⟩,Fin.ext (by dsimp [block]; omega)⟩

theorem cleaned_empty (a : Data) (ht : a.stacks 679=[]) : emptyRange (cleaned a) 417 680 := by
  intro i hi hj
  by_cases he : i=679
  · subst i
    change BankRoutines.clearBankStacks cleanupPorts a.stacks 679=[]
    rw [BankRoutines.clearBankStacks_frame]
    · exact ht
    · rw [cleanup_mem]; decide
  · apply BankRoutines.clearBankStacks_mem
    exact (cleanup_mem i).mpr (by omega)

theorem cleaned_frame (a : Data) (i : Fin 768) (hi : i.val < 417 ∨ 680 ≤ i.val) :
    (cleaned a).stacks i=a.stacks i := by
  apply BankRoutines.clearBankStacks_frame
  rw [cleanup_mem]
  omega

theorem cleaned_guard (a : Data) : (cleaned a).regs 8=a.regs 8 := by rfl

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
