import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramLookup
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-! Physical opening of an inline weighted clause record. The record payload is
`frame coefficient ++ encodeList encodeNat clause`. It is supplied reversed by
the outer record parser. Both the weight frame and the literal list are traversed
by fixed bit programs; source clause IDs are resolved by the upstream producer. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev Data := State 5 6

abbrev transfer : Cmd 5 6 :=
  .call (StackRoutines.transferProgram (0 : Fin 6) 2 (0 : Fin 5) 1)

theorem transfer_eval (regs : Fin 5 → Bool) (payload : List Bool) :
    Eval transfer (3*payload.length+3)
      (recordState regs payload.reverse [] [] [] [] [])
      (recordState (readRegs regs 0 1 none) [] [] payload [] [] []) := by
  let d := recordState regs payload.reverse [] [] [] [] []
  have h := StackRoutines.transferProgram_trace (0 : Fin 6) 2 (0 : Fin 5) 1
    (by decide) (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  have hs : StackRoutines.transferStacks (0 : Fin 6) 2 d.stacks =
      (recordState (readRegs regs 0 1 none) [] [] payload [] [] []).stacks := by
    funext i; fin_cases i <;> simp [d,StackRoutines.transferStacks]
  apply Eval.call
  simp only [StackRoutines.transferResult] at hh
  rw [hs] at hh
  simpa [d,recordState,storage,StructuredProgram.State.withPC,StackRoutines.transferProgram,
    Nat.add_assoc] using hh

abbrev openWeighted : Cmd 5 6 := .seq transfer (.call (parseFrame 2 5))

private theorem after_weight (regs : Fin 5 → Bool) (weight clause : List Bool) :
    afterFrame (recordState regs [] [] (Encoding.frame weight ++ clause) [] [] [])
      2 5 weight clause =
        recordState (readRegs regs 0 1 (some false)) [] [] clause [] [] weight.reverse := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp []

theorem openWeighted_eval (regs : Fin 5 → Bool) (weight clause : List Bool) :
    Eval openWeighted (3*(Encoding.frame weight ++ clause).length + 6*weight.length+7)
      (recordState regs (Encoding.frame weight ++ clause).reverse [] [] [] [] [])
      (recordState (readRegs (readRegs regs 0 1 none) 0 1 (some false))
        [] [] clause [] [] weight.reverse) := by
  have ht := transfer_eval regs (Encoding.frame weight ++ clause)
  have hp := parseFrame_eval (recordState (readRegs regs 0 1 none)
    [] [] (Encoding.frame weight ++ clause) [] [] []) 2 5 (by decide) weight clause rfl
  rw [after_weight] at hp
  convert ht.seq hp using 1 ; omega

def weightedPayload (weight : List Bool) (clause : List ℕ) : List Bool :=
  Encoding.frame weight ++ Encoding.encodeList Encoding.encodeNat clause

def openWeightedProgram := compiled openWeighted 0 2

/-- The entire supplied literal list is preserved literally. In particular,
this is not an evaluation or enumeration of the clause's joint scope. -/
theorem openWeighted_runs (regs : Fin 5 → Bool) (weight : List Bool) (clause : List ℕ) :
    RunsIn openWeightedProgram
      (3*(weightedPayload weight clause).length + 6*weight.length+8)
      ((recordState regs (weightedPayload weight clause).reverse [] [] [] [] []).withPC
        (some openWeightedProgram.entry))
      ((recordState (readRegs (readRegs regs 0 1 none) 0 1 (some false))
        [] [] (Encoding.encodeList Encoding.encodeNat clause) [] [] weight.reverse).withPC none) := by
  have he := openWeighted_eval regs weight (Encoding.encodeList Encoding.encodeNat clause)
  exact ⟨_,by dsimp [weightedPayload]; omega,compiled_halt_trace he 0 2⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Rows

end OAI.Algorithms
