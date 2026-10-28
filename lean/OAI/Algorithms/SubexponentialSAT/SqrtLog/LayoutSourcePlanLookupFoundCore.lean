import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram

namespace OAI.Algorithms

/-! The existing full-record scanner retains its successful-match bit. This
module exposes that bit without changing the machine or adding instructions. -/
namespace SubexponentialSAT.SubexpNodeIndexProgram.Internal
open BitProgram StructuredCalls SubexpScanPrimitives

theorem any_equal_mem (nodes : List (List Bool)) (query : List Bool) :
    nodes.any (fun key => decide (key=query))=decide (query ∈ nodes) := by
  induction nodes with
  | nil => rfl
  | cons a as ih =>
      by_cases h : a=query
      · subst a; simp
      · simp [h,Ne.symm h,ih]

theorem command_eval_found (regs : Fin 5 → Bool) (query : List Bool) (nodes : List (List Bool)) :
    ∃ n, n + 1 ≤ budget query nodes ∧ ∃ regs',
      Eval command n (state regs query (ProgramEncoding.encodeRecords nodes) [] [] [] [] [])
        (state regs' query (ProgramEncoding.encodeRecords nodes) [] [] [] []
          (List.replicate (nodes.idxOf query) true)) ∧
      regs' 4=decide (query ∈ nodes) := by
  let master := ProgramEncoding.encodeRecords nodes
  let d := state regs query master [] [] [] [] []
  let rr := readRegs regs 0 1 none
  have hc := copy_eval d 1 2 5 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have hcEnd : afterCopy d 1 2 0 1 = state rr query master master [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [d,afterCopy,StackRoutines.copyStacks,state,store]
  have hcLen : (d.stacks 1).length = master.length := rfl
  rw [hcEnd,hcLen] at hc
  let base := state rr query master [] [] [] [] []
  obtain ⟨ns,next,hns,hnext,hvis,hs⟩ := RecordPrograms.iterate_run_with ports callback
    (fun key => decide (key = query)) (callbackCost query) (invariant query master)
    (effect query) (callback_contract query master) nodes [] base ⟨rr,[],rfl⟩
      (rr 0) (rr 1) (rr 4)
  have hcount := visits_count query hvis
  obtain ⟨rs,count,hnext⟩ := hnext
  rw [hnext] at hs hcount
  have hcount' : count = List.replicate (nodes.idxOf query) true := by
    change count = List.replicate (nodes.idxOf query) true ++ [] at hcount
    simpa only [List.append_nil] using hcount
  subst count
  let tail := RecordPrograms.unread (fun key => decide (key = query)) nodes []
  let rs' := normalized rs false true (nodes.any (fun key => decide (key = query)))
  have hs' : Eval (RecordPrograms.iterate ports callback) ns
      (state rr query master master [] [] [] [])
      (state rs' query master tail [] [] [] (List.replicate (nodes.idxOf query) true)) := by
    simpa only [base,outer_state,normalized_self,List.append_nil,master,
      ProgramEncoding.encodeRecords,rs',tail] using hs
  let e := state rs' query master tail [] [] [] (List.replicate (nodes.idxOf query) true)
  have hz := clear_eval e 2
  have hzEnd : cleared e 2 = state (readRegs rs' 0 1 none) query master [] [] [] []
      (List.replicate (nodes.idxOf query) true) := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [e,cleared,state,store]
  have hzLen : (e.stacks 2).length = tail.length := rfl
  rw [hzEnd,hzLen] at hz
  have htail := unread_length query nodes
  have hcost := RecordPrograms.program_budget_le_input (callbackCost query) nodes
    20 (9*query.length+32) (fun key _ => by simp [callbackCost,Nat.add_assoc])
  refine ⟨(7*master.length+5)+(ns+(2*tail.length+3)),?_,readRegs rs' 0 1 none,?_,?_⟩
  · change tail.length ≤ master.length at htail
    change 4 + RecordPrograms.budget (callbackCost query) nodes ≤
      (20+(9*query.length+32)+17)*(master.length+1) at hcost
    unfold budget
    change _ ≤ (9*query.length+80)*(master.length+1)
    nlinarith
  · exact hc.seq (hs'.seq hz)

  · simpa [readRegs,rs',normalized] using any_equal_mem nodes query

end SubexponentialSAT.SubexpNodeIndexProgram.Internal

end OAI.Algorithms
