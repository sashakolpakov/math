import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramMemory

namespace OAI.Algorithms

/-! Exact frame for unpacking an inline weighted clause into the two physical
operands used by the clause loop and weighted accumulator. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

structure WeightedReady (d : Machine) : Prop where
  temporary : d.stacks 57 = []
  clause : d.stacks 63 = []
  compare : d.stacks 59 = []
  scratch : d.stacks 60 = []
  weight : d.stacks 65 = []

def rowCallerRegs (d : Machine) : Fin 5 → Bool := fun i => d.regs (rowRegisters i)

theorem project_weighted (d : Machine) (payload : List Bool)
    (h : WeightedReady d) (hp : d.stacks 66 = payload) :
    projectState rowRegisters rowStacks d =
      SubexponentialSAT.SubexpRecordScan.recordState (rowCallerRegs d) payload [] [] [] [] [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i
    · exact hp
    · exact h.temporary
    · exact h.clause
    · exact h.compare
    · exact h.scratch
    · exact h.weight

def openedHigh (high : Fin 40 → List Bool) (clause weight : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update high 10 []) 1 []) 7 clause) 3 []) 4 []) 9 weight

theorem rowFrame_memory (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (rr : Fin 5 → Bool) (clause weight : List Bool) :
    let out := rowFrame (Memory.state regs low high) rr [] clause weight
    out = Memory.state out.regs low (openedHigh high clause weight) := by
  dsimp only
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    induction i using (Fin.addCases (m := 56) (n := 40)) with
    | left i =>
      have h := rowFrame_stack (Memory.state regs low high) rr [] clause weight
        (Fin.castAdd 40 i) (Or.inl i.isLt)
      simpa [rowFrame, embedState, Memory.state,Memory.tapes] using h
    | right i =>
      rw [Memory.tapes, Fin.addCases_right]
      have hp (j : Fin 6) := embedState_stack rowRegisters rowStacks (Memory.state regs low high)
        (SubexponentialSAT.SubexpRecordScan.recordState rr [] [] clause [] [] weight) rowStacks_injective j
      have hf (j : Fin 96) (hj : ¬ ∃ k, rowStacks k = j) :=
        embedState_stack_frame rowRegisters rowStacks (Memory.state regs low high)
          (SubexponentialSAT.SubexpRecordScan.recordState rr [] [] clause [] [] weight) j hj
      have hf_high (j : Fin 40) (hj : ¬ ∃ k, rowStacks k = Fin.natAdd 56 j) :
          Function.extend rowStacks
              (SubexponentialSAT.SubexpRecordScan.recordState rr [] [] clause [] [] weight).stacks
              (Memory.state regs low high).stacks (Fin.natAdd 56 j) = high j := by
        calc
          _ = (Memory.state regs low high).stacks (Fin.natAdd 56 j) :=
            hf (Fin.natAdd 56 j) hj
          _ = high j := by simp [Memory.state, Memory.tapes]
      fin_cases i
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (0 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 1
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (2 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 3
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 4
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (5 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (6 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 2
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (8 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 5
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 0
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (11 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (12 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (13 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (14 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (15 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (16 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (17 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (18 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (19 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (20 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (21 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (22 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (23 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (24 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (25 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (26 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (27 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (28 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (29 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (30 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (31 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (32 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (33 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (34 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (35 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (36 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (37 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (38 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (39 : Fin 40) (by decide)

theorem openWeighted_from_state (d : Machine) (weight clause : List Bool)
    (h : WeightedReady d) (hp : d.stacks 66 = (Encoding.frame weight ++ clause).reverse) :
    let rr := readRegs (readRegs (rowCallerRegs d) 0 1 none) 0 1 (some false)
    Eval openWeighted (3*(Encoding.frame weight ++ clause).length+6*weight.length+8)
      d (rowFrame d rr [] clause weight.reverse) := by
  dsimp only
  have he := Rows.openWeighted_eval (rowCallerRegs d) weight clause
  rw [← project_weighted d _ h hp] at he
  have hh := eval_liftCommand_from_state Rows.openWeighted 0 2 rowRegisters rowStacks d
    rowRegisters_injective rowStacks_injective he
  simpa only [Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
