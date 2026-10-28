import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCode

namespace OAI.Algorithms

/-! Exact physical boundaries for the clause counter, trivial dispatch, and
the final Boolean decision. None of these steps invokes an evaluator oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls

theorem clauseCount_eval (a : Data) (records : List (List Bool))
    (hformula : a.stacks 784 = Encoding.encodeList id records)
    (hempty : ∀ i : Fin 896, i.val < 14 → a.stacks i = [])
    (h782 : a.stacks 782 = []) :
    ∃ n b, Eval LeafProgram.ClauseCount.caller n a b ∧
      n ≤ LeafProgram.ClauseCount.budget records+1 ∧
      BinaryArithmetic.toNat (b.stacks 782) = records.length ∧
      (b.stacks 782).length ≤ records.length ∧
      (∀ i : Fin 896, i ≠ 782 → b.stacks i = a.stacks i) := by
  let reg := LeafProgram.ClauseCount.callerRegisters
  let stk := LeafProgram.ClauseCount.callerStacks
  have hr : Function.Injective reg := Fin.castAdd_injective 8 32
  have hs : Function.Injective stk := by decide
  have hp : projectState reg stk a = LeafProgram.ClauseCount.data (a.regs ∘ reg)
      (Encoding.encodeList id records) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [stk,LeafProgram.ClauseCount.callerStacks,
hformula,h782,hempty]
  obtain ⟨n,word,rr,hn,hv,hl,he⟩ := LeafProgram.ClauseCount.command_eval (a.regs ∘ reg) records
  have ht := compiled_halt_trace he 1 15
  rw [← hp] at ht
  let out := LeafProgram.ClauseCount.data rr (Encoding.encodeList id records) [] word
  let b := embedState reg stk a out
  have hb782 : b.stacks 782 = word := embedState_stack reg stk a out hs 15
  refine ⟨n+1,b,eval_call_from_state _ reg stk a hr hs ht,by omega,
    by simpa only [hb782] using hv,by simpa only [hb782] using hl,?_⟩
  intro i hi
  by_cases hport : ∃ j, stk j = i
  · obtain ⟨j,rfl⟩ := hport
    have hj15 : j ≠ 15 := by intro h; subst j; exact hi rfl
    rw [embedState_stack reg stk a out hs]
    have hproj := congrArg (fun d : State 8 16 => d.stacks j) hp
    change a.stacks (stk j) = _ at hproj
    rw [hproj]
    fin_cases j <;> simp_all [out,LeafProgram.ClauseCount.data]
  · exact embedState_stack_frame reg stk a out i hport

theorem decideCount_eval (a : Data) (hempty : a.stacks 787 = []) :
    ∃ n b, Eval decideCount n a b ∧ n ≤ 5*(a.stacks 788).length+11 ∧
      b.stacks 787 = [PositiveWordProgram.positive (a.stacks 788)] ∧
      b.stacks 788 = [] ∧
      (∀ i, i ≠ 787 → i ≠ 788 → b.stacks i = a.stacks i) := by
  have hr : Function.Injective decisionRegisters := Fin.castAdd_injective 2 38
  have hs : Function.Injective decisionStacks := by decide
  have hp : projectState decisionRegisters decisionStacks a =
      LeafProgram.Decision.data (PositiveWordProgram.regs (a.regs 0) (a.regs 1))
        (a.stacks 788) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [decisionStacks,hempty]
  obtain ⟨n,hn,ht⟩ := LeafProgram.Decision.program_run (a.stacks 788) (a.regs 0) (a.regs 1)
  rw [← hp] at ht
  let out := LeafProgram.Decision.data (fun _ => false) []
    [PositiveWordProgram.positive (a.stacks 788)]
  let b := embedState decisionRegisters decisionStacks a out
  refine ⟨n,b,eval_call_from_state _ _ _ _ hr hs ht,hn,?_,?_,?_⟩
  · exact embedState_stack decisionRegisters decisionStacks a out hs 1
  · exact embedState_stack decisionRegisters decisionStacks a out hs 0
  · intro i h787 h788
    apply embedState_stack_frame
    rintro ⟨j,hj⟩
    fin_cases j
    · exact h788 hj.symm
    · exact h787 hj.symm

noncomputable def classified (a : Data) (records : List (List Bool)) : Data :=
  LeafProgram.Dispatch.install a (LeafProgram.Trivial.result
    (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a) records)

theorem classified_stacks (a : Data) (records : List (List Bool)) :
    (classified a records).stacks = a.stacks := by
  have h := embedState_project LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a
    LeafProgram.Dispatch.registers_injective LeafProgram.Dispatch.stackMap_injective
  change (embedState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a
    (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a)).stacks=a.stacks
  exact congrArg StructuredProgram.State.stacks h

theorem classify_eval (a : Data) (records : List (List Bool))
    (hformula : a.stacks 784 = Encoding.encodeList id records)
    (hready : SubexpEmptyClauseProgram.Ready
      (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a)) :
    ∃ n ≤ 100*((a.stacks 784).length+1)+3,
      Eval LeafProgram.Dispatch.classify n a (classified a records) := by
  obtain ⟨n,hn,he⟩ := LeafProgram.Dispatch.classify_run a
    (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a) records hformula hready
  have hp : LeafProgram.Dispatch.install a
      (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a)=a :=
    embedState_project _ _ a LeafProgram.Dispatch.registers_injective LeafProgram.Dispatch.stackMap_injective
  rw [hp] at he
  exact ⟨n,hn,he⟩

theorem dispatch_nontrivial (mass acceptedCount : Cmd 40 896) (a : Data)
    (records : List (List Bool)) (hformula : a.stacks 784 = Encoding.encodeList id records)
    (hready : SubexpEmptyClauseProgram.Ready
      (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a))
    (hempty : [false] ∉ records) (hnonempty : records ≠ [])
    {steps : ℕ} {b : Data} (he : Eval (nontrivial mass acceptedCount) steps (classified a records) b) :
    ∃ n ≤ 100*((a.stacks 784).length+1)+5+steps,
      Eval (command mass acceptedCount) n a b := by
  obtain ⟨nc,hnc,hc⟩ := classify_eval a records hformula hready
  have h0 : (classified a records).regs 0 = false := by
    rw [classified,LeafProgram.Dispatch.result_empty_clause]
    exact decide_eq_false hempty
  have h7 : (classified a records).regs 7 = true := by
    rw [classified,LeafProgram.Dispatch.result_nonempty]
    exact decide_eq_true hnonempty
  exact ⟨nc+(steps+1+1),by omega,hc.seq (.ite_false h0 (.ite_true h7 he))⟩

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
