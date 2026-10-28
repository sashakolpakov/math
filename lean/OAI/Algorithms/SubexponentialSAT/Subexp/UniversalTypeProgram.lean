import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeEnumeration

namespace OAI.Algorithms

/-! Actual universal-type generation from the saved word alphabet and unary
slot count. The extra head coordinate is installed by one real push. -/

namespace SubexponentialSAT.Subexp.UniversalTypeProgram

open BitProgram StructuredCalls TupleProgram

def inputState (alphabet : Records) (depth : List Bool) (regs : Fin 10 → Bool) : State 10 9 :=
  ⟨regs, ![[], ProgramEncoding.encodeRecords alphabet, [], [], [], [], [], [], depth]⟩

def outputState (alphabet rows : Records) (regs : Fin 10 → Bool) : State 10 9 :=
  ⟨regs, ![ProgramEncoding.encodeRecords rows, ProgramEncoding.encodeRecords alphabet,
    [], [], [], [false], [], [], []]⟩

abbrev command : Cmd 10 9 :=
  .seq (pushConst 8 6 true) (.call generateProgram)

def program := compiled command 1 0

def budget (alphabet : Records) (slots : ℕ) : ℕ :=
  powerCost alphabet (slots + 1) [[]] + 12

theorem ready_eq (alphabet rows : Records) (a : State 10 9)
    (ha : Ready alphabet rows [] false a) : a = outputState alphabet rows a.regs := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  rcases ha with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
  fin_cases i <;> simp [h0,h1,h2,h3,h4,h5,h6,h7,h8]

theorem program_runsIn (alphabet : Records) (depth : List Bool) (regs : Fin 10 → Bool) :
    ∃ nextRegs, RunsIn program (budget alphabet depth.length)
      ((inputState alphabet depth regs).withPC (some program.entry))
      ((outputState alphabet (powerRows alphabet (depth.length + 1) [[]]) nextRegs).withPC none) := by
  let a := inputState alphabet depth regs
  let b := pushedState 8 6 true a
  have hb : outerInvariant alphabet (true :: depth) (regs 9) b := by
    simp [outerInvariant,b,a,inputState]
  obtain ⟨next,hn, n, hbound, ht⟩ := generateProgram_runsIn alphabet (true :: depth) (regs 9) b hb
    (by simp [b,a,inputState])
    (by simp [b,a,inputState])
    (by simp [b,a,inputState])
  have he : Eval command (2 + n) a next := (pushConst_eval 8 6 true a).seq (.call _ ht)
  have hout := ready_eq alphabet (powerRows alphabet (depth.length + 1) [[]]) next
    (by simpa only [List.length_cons] using hn)
  rw [hout] at he
  refine ⟨next.regs, 2 + n + 1, ?_, compiled_halt_trace he 1 0⟩
  simp only [List.length_cons] at hbound
  dsimp [budget]
  omega

theorem universal_runsIn (r Q Δ : ℕ) (regs : Fin 10 → Bool) :
    ∃ nextRegs, RunsIn program (budget (AssignmentAlphabetSemantics.wordBytes r Q) Δ)
      ((inputState (AssignmentAlphabetSemantics.wordBytes r Q) (List.replicate Δ true) regs).withPC
        (some program.entry))
      ((outputState (AssignmentAlphabetSemantics.wordBytes r Q)
        (TypeEnumeration.universalBytes r Q Δ) nextRegs).withPC none) := by
  simpa [TypeEnumeration.universalBytes] using program_runsIn
    (AssignmentAlphabetSemantics.wordBytes r Q) (List.replicate Δ true) regs

end SubexponentialSAT.Subexp.UniversalTypeProgram

end OAI.Algorithms
