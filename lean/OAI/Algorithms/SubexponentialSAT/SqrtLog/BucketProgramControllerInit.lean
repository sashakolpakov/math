import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramEnumeration
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! A fixed runtime head enumerator with an explicit persistent bucket frame. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Controller
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 10 24
abbrev Code := Cmd 10 24

def state (regs : Fin 10 → Bool) (W rows js n pending records keys output alphabet depth : List Bool) : Data :=
  ⟨regs, ![W,[],[],[],[],[],[],[],[],[],[],[],[],[],[],pending,rows,js,n,records,keys,output,alphabet,depth]⟩

def pushFixed (dst : Fin 24) : List Bool → Code
  | [] => .base .skip
  | b::bs => .seq (pushFixed dst bs) (SubexponentialSAT.Subexp.TupleProgram.pushConst dst 0 b)

theorem pushFixed_eval (dst : Fin 24) (bits : List Bool) (d : Data) :
    ∃ rf, Eval (pushFixed dst bits) (2*bits.length) d
      ⟨rf, Function.update d.stacks dst (bits++d.stacks dst)⟩ := by
  induction bits generalizing d with
  | nil =>
      refine ⟨d.regs,?_⟩
      simpa [pushFixed] using Eval.base (StructuredProgram.Eval.skip d)
  | cons b bs ih =>
      obtain ⟨rf,he⟩ := ih d
      have hp := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval dst (0 : Fin 10) b
        (⟨rf, Function.update d.stacks dst (bs++d.stacks dst)⟩ : Data)
      refine ⟨Function.update rf 0 b,?_⟩
      simpa [pushFixed,SubexponentialSAT.Subexp.TupleProgram.pushedState,Nat.mul_add,Nat.add_assoc] using he.seq hp

def enumPorts : Fin 9 → Fin 24 := ![15,22,1,2,3,4,5,6,23]
theorem enumPorts_injective : Function.Injective enumPorts := by decide

def enumCall : Code := .call (ProgramLinking.liftProgram enumerationProgram id enumPorts)
def initCommand : Code := .seq (pushFixed 22 (ProgramEncoding.encodeRecords alphabet)) (pushFixed 20 [false])
def enumerate : Code := .seq initCommand (.seq enumCall (WorkspaceCleanupProgram.command 0 1 [4,22]))

def input (regs : Fin 10 → Bool) (W rows js n : List Bool) (h : ℕ) : Data :=
  state regs W rows js n [] [] [] [] [] (List.replicate h false)

def enumerated (regs : Fin 10 → Bool) (W rows js n : List Bool) (h : ℕ) : Data :=
  state regs W rows js n (ProgramEncoding.encodeRecords (assignments h)) [] [false] [] [] []

def enumerateCost (h : ℕ) : ℕ := enumerationCost h + 48

theorem enumerate_eval (regs : Fin 10 → Bool) (W rows js n : List Bool) (h : ℕ) :
    ∃ t ≤ enumerateCost h, ∃ rf,
      Eval enumerate t (input regs W rows js n h) (enumerated rf W rows js n h) := by
  let d := input regs W rows js n h
  obtain ⟨ra,hea⟩ := pushFixed_eval 22 (ProgramEncoding.encodeRecords alphabet) d
  let a : Data := ⟨ra,Function.update d.stacks 22 (ProgramEncoding.encodeRecords alphabet)⟩
  have hea' : Eval (pushFixed 22 (ProgramEncoding.encodeRecords alphabet)) 18 d a := by
    simpa [a,d,input,state,alphabet,ProgramEncoding.encodeRecords,Encoding.encodeList,Encoding.frame] using hea
  obtain ⟨rb,heb⟩ := pushFixed_eval 20 [false] a
  let b : Data := state rb W rows js n [] [] [false] []
    (ProgramEncoding.encodeRecords alphabet) (List.replicate h false)
  have heb' : Eval (pushFixed 20 [false]) 2 a b := by
    convert heb using 1
    apply congrArg (StructuredProgram.State.mk rb)
    funext i; fin_cases i <;> simp [a,d,input,state]
  let aLocal := projectState id enumPorts b
  have hi : SubexponentialSAT.Subexp.TupleProgram.outerInvariant alphabet (List.replicate h false) (rb 9) aLocal := by
    simp [aLocal,projectState,enumPorts,b,state,SubexponentialSAT.Subexp.TupleProgram.outerInvariant]
  obtain ⟨e,he,k,hk,ht⟩ := SubexponentialSAT.Subexp.TupleProgram.generateProgram_runsIn alphabet
    (List.replicate h false) (rb 9) aLocal hi
    (by simp [aLocal,projectState,enumPorts,b,state])
    (by simp [aLocal,projectState,enumPorts,b,state])
    (by simp [aLocal,projectState,enumPorts,b,state])
  have hcall := eval_call_from_state enumerationProgram id enumPorts b
    Function.injective_id enumPorts_injective ht
  let c : Data := ⟨e.regs,Function.update
    (state e.regs W rows js n (ProgramEncoding.encodeRecords (assignments h)) [] [false] []
      (ProgramEncoding.encodeRecords alphabet) []).stacks 4 [false]⟩
  have hc : embedState id enumPorts b e=c := by
    rcases he with ⟨⟨he1,he3,he4,he6,he7,he8,he9⟩,he0,he2,he5⟩
    apply embedState_eq_of_ports id enumPorts b c e Function.injective_id enumPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;>
        simp_all [c,enumPorts,state,assignments]
    · intro i hi
      fin_cases i <;> simp_all [Fin.exists_fin_succ,enumPorts,c,b,state]
  change Eval enumCall k b (embedState id enumPorts b e) at hcall
  rw [hc] at hcall
  have hclean := WorkspaceCleanupProgram.command_eval (0 : Fin 10) 1
    ([4,22] : List (Fin 24)) (by decide) c
  have hfinish : WorkspaceCleanupProgram.finish (0 : Fin 10) 1 ([4,22] : List (Fin 24)) c =
      enumerated (WorkspaceCleanupProgram.finish 0 1 ([4,22] : List (Fin 24)) c).regs W rows js n h := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> simp [c,state,BankRoutines.clearBankStacks]
  rw [hfinish] at hclean
  refine ⟨(18+2)+(k+WorkspaceCleanupProgram.cost ([4,22] : List (Fin 24)) c),?_,(WorkspaceCleanupProgram.finish 0 1 ([4,22] : List (Fin 24)) c).regs,?_⟩
  · have hb := SubexponentialSAT.Subexp.PackingTupleBounds.generated_powerCost_le alphabet h 1
      (by intro word hw; simp [alphabet] at hw; rcases hw with rfl | rfl <;> simp)
    simp only [List.length_replicate] at hk
    have hk' : k ≤ enumerationCost h := by
      exact hk.trans (by simpa [enumerationCost,alphabet] using Nat.add_le_add_right hb 9)
    simp [WorkspaceCleanupProgram.cost,c,state,alphabet,ProgramEncoding.encodeRecords,
      Encoding.encodeList,Encoding.frame,enumerateCost]
    omega
  · exact (hea'.seq heb').seq (hcall.seq hclean)

end SubexponentialSAT.SqrtLog.BucketProgram.Controller

end OAI.Algorithms
