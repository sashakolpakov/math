import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramLiteralState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramMemory

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The fetcher resets its six work words and retains the saved incidence table. -/
def literalHigh (high : Fin 40 → List Bool) (payload table : List Bool) : Fin 40 → List Bool :=
  fun i => Fin.addCases (m := 7) (n := 33) ![[],[],[],[],[],payload,table] (fun j => high (Fin.natAdd 7 j)) i

theorem literalFrame_memory (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (rr : Fin 5 → Bool) (positive : Bool) (payload table : List Bool) :
    let d := Memory.state regs low high
    let result := literalFrame d rr positive [] [] payload table
    result = Memory.state result.regs low (literalHigh high payload table) := by
  dsimp only
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    induction i using (Fin.addCases (m := 56) (n := 40)) with
    | left i =>
      have h := literalFrame_stack (Memory.state regs low high) rr positive [] [] payload table
        (Fin.castAdd 40 i) (Or.inl i.isLt)
      simpa [literalFrame, embedState, Memory.state, Memory.tapes] using h
    | right i =>
      rw [Memory.tapes, Fin.addCases_right]
      refine Fin.addCases (m := 7) (n := 33) (fun j => ?_) (fun j => ?_) i
      · rw [literalHigh, Fin.addCases_left]
        have h := embedState_stack literalRegisters literalStacks (Memory.state regs low high)
          (data rr positive [] [] payload table) literalStacks_injective j
        fin_cases j <;> simpa [literalFrame, embedState, literalHigh, Memory.state, Memory.tapes,
          Fin.addCases_left, Fin.addCases_right,
          literalStacks, data, extend, SubexponentialSAT.SubexpRecordScan.recordState,
          SubexponentialSAT.SubexpRecordScan.storage] using h
      · have h := literalFrame_stack (Memory.state regs low high) rr positive [] [] payload table
          (Fin.natAdd 56 (Fin.natAdd 7 j)) (Or.inr (by simp; omega))
        simpa [literalFrame, embedState, literalHigh, Memory.state, Memory.tapes] using h

theorem literalHigh_outside (high : Fin 40 → List Bool) (payload table : List Bool)
    (i : Fin 40) (hi : 7 ≤ i.val) : literalHigh high payload table i = high i := by
  induction i using (Fin.addCases (m := 7) (n := 33)) with
  | left i => have := i.isLt; change 7 ≤ i.val at hi; omega
  | right i => simp [literalHigh]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
