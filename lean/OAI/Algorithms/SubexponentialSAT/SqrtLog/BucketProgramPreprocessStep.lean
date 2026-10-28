import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramShift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPreprocessReverse
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Concrete decoding and shifting of one signed coefficient pair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev SignedWord := List Bool × List Bool
abbrev PreData := State 8 14
abbrev PreCode := Cmd 8 14

def signedWords : List SignedWord → List Bool
  | [] => []
  | (P,N)::xs => Encoding.frame P ++ Encoding.frame N ++ signedWords xs

def preState (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord)
    (out : List Bool) : PreData :=
  ⟨regs, ![W,[],[],[],[],[],[],[],[],[],signedWords xs,out,[],[]]⟩

def preShiftPort : Fin 10 → Fin 14 := Fin.castAdd 4
def preShiftCall : PreCode := .call
  (ProgramLinking.liftProgram shiftProgram id preShiftPort)

def preStep : PreCode :=
  .seq (readWord 10 8 12 (by decide))
    (.seq (readWord 10 1 12 (by decide))
      (.seq preShiftCall (.seq (WorkspaceCleanupProgram.command 0 1 [1,2,8])
        (emitFrame 9 11 12 (by decide)))))

def shiftedWord (W : List Bool) (a : SignedWord) (out : List Bool) : Prop :=
  SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat W -
    SubexponentialSAT.BinaryArithmetic.toNat a.2 + SubexponentialSAT.BinaryArithmetic.toNat a.1 ∧
  out.length ≤ W.length+a.2.length+a.1.length+1

def preStepCost (W : List Bool) (a : SignedWord) : ℕ :=
  600*(W.length+a.2.length+a.1.length+1)^2+100

theorem preStep_eval (regs : Fin 8 → Bool) (W P N : List Bool)
    (xs : List SignedWord) (out : List Bool) :
    ∃ t ≤ preStepCost W (P,N), ∃ rf word,
      Eval preStep t (preState regs W ((P,N)::xs) out)
        (preState rf W xs (Encoding.frame word++out)) ∧ shiftedWord W (P,N) word := by
  let d := preState regs W ((P,N)::xs) out
  obtain ⟨a,ha,hsa⟩ := readWord_eval (10 : Fin 14) 8 12
    (by decide) (by decide) (by decide) d P (Encoding.frame N++signedWords xs)
    (by simp [d,preState,signedWords,List.append_assoc]) rfl rfl
  obtain ⟨b,hb,hsb⟩ := readWord_eval (10 : Fin 14) 1 12
    (by decide) (by decide) (by decide) a N (signedWords xs)
    (by rw [hsa]; rfl) (by rw [hsa]; rfl) (by rw [hsa]; rfl)
  have hproj : projectState id preShiftPort b = shiftState b.regs W N P [] [] := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i; fin_cases i <;> simp [preShiftPort,hsb,hsa,d,preState]
  obtain ⟨ts,hts,rs,diff,word,hes,hvs,hls,hld⟩ := shiftCommand_eval_lengths b.regs W N P
  rw [←hproj] at hes
  have hcall := eval_call_from_state shiftProgram id preShiftPort b
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hes 0 9)
  let c : PreData := ⟨rs,Function.update (Function.update b.stacks 2 diff) 9 word⟩
  have hembed : embedState id preShiftPort b (shiftState rs W N P diff word)=c := by
    apply embedState_eq_of_ports id preShiftPort b _ _ Function.injective_id
      (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [c,preShiftPort,shiftState,hsb,hsa,d,preState]
    · intro i hi
      have h2 : i≠2 := fun h => hi ⟨2,h.symm⟩
      have h9 : i≠9 := fun h => hi ⟨9,h.symm⟩
      simp [c,h2,h9]
  change Eval preShiftCall (ts+1) b
    (embedState id preShiftPort b (shiftState rs W N P diff word)) at hcall
  rw [hembed] at hcall
  let e := WorkspaceCleanupProgram.finish (0 : Fin 8) 1 ([1,2,8] : List (Fin 14)) c
  have he := WorkspaceCleanupProgram.command_eval (0 : Fin 8) 1
    ([1,2,8] : List (Fin 14)) (by decide) c
  obtain ⟨f,hf,hsf⟩ := emitFrame_eval (9 : Fin 14) 11 12
    (by decide) (by decide) (by decide) e (by simp [e,c,hsb,hsa,d,preState])
  have he9 : e.stacks 9=word := by simp [e,c]
  have hend : f=preState f.regs W xs (Encoding.frame word++out) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i; fin_cases i <;> simp [e,c,hsb,hsa,d,preState]
  have hcCost : WorkspaceCleanupProgram.cost ([1,2,8] : List (Fin 14)) c =
      2*(N.length+diff.length+P.length)+9 := by
    simp [WorkspaceCleanupProgram.cost,c,hsb,hsa,d,preState]; omega
  have hall := ha.seq (hb.seq (hcall.seq (he.seq hf)))
  rw [hend] at hall
  refine ⟨_,?_,f.regs,word,hall,hvs,hls⟩
  rw [hcCost,he9]
  dsimp [preStepCost]
  nlinarith [Nat.zero_le W.length,Nat.zero_le N.length,Nat.zero_le P.length]

theorem shiftedWord_integer (W : List Bool) (a : SignedWord) (word : List Bool)
    (h : shiftedWord W a word)
    (hNW : SubexponentialSAT.BinaryArithmetic.toNat a.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W) :
    (SubexponentialSAT.BinaryArithmetic.toNat word : ℤ) = (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ) +
      ((SubexponentialSAT.BinaryArithmetic.toNat a.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat a.2 : ℤ)) := by
  rw [h.1]
  exact shift_value_integer _ _ _ hNW

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
