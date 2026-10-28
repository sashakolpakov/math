import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientCheckerExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchSemantics

namespace OAI.Algorithms

/-! Fixed first-success control for normalized coefficient search. All
candidate, interval, and field sizes remain encoded runtime data. -/

namespace SubexponentialSAT.Subexp.CoefficientSearchProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls SubexpScanPrimitives MatrixWordEncoding

abbrev Data := State 14 32

def checkerRegisters (i : Fin 11) : Fin 14 := Fin.castAdd 3 i
def checkerStacks (i : Fin 20) : Fin 32 := Fin.castAdd 12 i
def tupleRegisters (i : Fin 10) : Fin 14 := Fin.castAdd 4 i
def tupleStacks : Fin 9 → Fin 32 := ![22,25,23,26,27,28,24,29,30]

theorem checkerRegisters_injective : Function.Injective checkerRegisters := Fin.castAdd_injective _ _
theorem checkerStacks_injective : Function.Injective checkerStacks := Fin.castAdd_injective _ _
theorem tupleRegisters_injective : Function.Injective tupleRegisters := Fin.castAdd_injective _ _
theorem tupleStacks_injective : Function.Injective tupleStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [tupleStacks]

def ports : RecordPrograms.Ports 14 32 :=
  ⟨11,12,13,22,23,by decide,by decide,by decide,by decide⟩

abbrev copy (src dst : Fin 32) : Cmd 14 32 :=
  .call (StackRoutines.copyProgram src dst 24 11 12)
abbrev clear (src : Fin 32) : Cmd 14 32 :=
  .call (StackRoutines.clearProgram src 11 12)
abbrev transfer (src dst : Fin 32) : Cmd 14 32 :=
  .call (StackRoutines.transferProgram src dst 11 12)

abbrev checker : Cmd 14 32 :=
  .call (ProgramLinking.liftProgram CoefficientCheckerProgram.program checkerRegisters checkerStacks)

abbrev callback : Cmd 14 32 :=
  .seq (clear 21) (.seq (transfer 23 12) (.seq (copy 12 21) (.seq (copy 31 17)
    (.seq checker (.seq (.base (.atom (.bor 13 10 10)))
      (.seq (clear 12) (.base (.atom (.set 12 true)))))))))

abbrev generate : Cmd 14 32 :=
  .seq (copy 16 30) (.seq
    (.call (ProgramLinking.liftProgram TupleProgram.generateProgram tupleRegisters tupleStacks))
    (clear 28))

abbrev search : Cmd 14 32 := RecordPrograms.iterate ports callback

abbrev command : Cmd 14 32 := .seq generate search

def program := compiled command 25 21

/-- Shape of the caller frame around the low checker service. -/
def wide (low : CoefficientCheckerProgram.Data) (tag present found : Bool)
    (selected source payload alphabet advanceTemplate : List Bool) : Data :=
  ⟨Fin.addCases (m := 11) (n := 3) (motive := fun _ => Bool) low.regs ![tag,present,found],
    Fin.addCases (m := 20) (n := 12) (motive := fun _ => List Bool) low.stacks
      ![[],selected,source,payload,[],alphabet,[],[],[],[],[],advanceTemplate]⟩

theorem embed_wide (before after : CoefficientCheckerProgram.Data) (tag present found : Bool)
    (selected source payload alphabet advanceTemplate : List Bool) :
    embedState checkerRegisters checkerStacks
      (wide before tag present found selected source payload alphabet advanceTemplate) after =
      wide after tag present found selected source payload alphabet advanceTemplate := by
  apply embedState_eq checkerRegisters checkerStacks checkerRegisters_injective checkerStacks_injective
  · intro i
    simp [wide,checkerRegisters]
  · intro i
    simp [wide,checkerStacks]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 11) (n := 3) (fun i => ?_) (fun i => ?_) j
    · intro hi
      exact (hi ⟨i,rfl⟩).elim
    · intro _
      simp [wide]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 20) (n := 12) (fun i => ?_) (fun i => ?_) j
    · intro hi
      exact (hi ⟨i,rfl⟩).elim
    · intro _
      simp [wide]

variable (p : ℕ) [Fact p.Prime]

def blank (R : ℕ) (regs : Fin 8 → Bool) (g neg ok : Bool) : CoefficientCheckerProgram.Data :=
  CoefficientCheckerProgram.wide (CoefficientCheckerProgram.lowData p regs [] [] []) g neg ok
    (List.replicate R true) [] [] (word p 1)

def callbackBudget (A R B : ℕ) : ℕ := CoefficientCheckerProgram.checkerBudget A R B + 14 * (R * (2 * B + 1)) + 7 * A + 21

/-- The executable candidate payload is the same framed coefficient list
consumed by the checker. -/
theorem encode_eq_valueWords {R : ℕ} (v : Fin R → ZMod p) :
    CoefficientSearchSemantics.encode p v = CoefficientPascalProgram.valueWords p (List.ofFn v) := by
  rw [CoefficientSearchSemantics.encode,BlockSearchPredicate.encoded_vector_eq_words]
  simp only [CoefficientPascalProgram.valueWords,List.map_ofFn,Function.comp_def]

/-- A checker call preserves the complete search frame, including the saved
unshifted candidate and unread candidate records. -/
theorem checker_eval (A : ℕ) (xs : List (ZMod p)) (regs : Fin 8 → Bool)
    (g neg ok tag present found : Bool)
    (selected source payload alphabet : List Bool) :
    ∃ n ≤ CoefficientCheckerProgram.checkerBudget A xs.length (width p), ∃ regs',
      Eval checker n
        (wide (CoefficientCheckerProgram.ready p regs g neg ok xs (List.replicate A true) [])
          tag present found selected source payload alphabet (List.replicate A true))
        (wide (CoefficientCheckerProgram.outputState p A xs regs')
          tag present found selected source payload alphabet (List.replicate A true)) := by
  obtain ⟨r,n,hn,ht⟩ := CoefficientCheckerProgram.program_run p A xs regs g neg ok
  have he := eval_call_lifted CoefficientCheckerProgram.program checkerRegisters checkerStacks
    (wide (CoefficientCheckerProgram.ready p regs g neg ok xs (List.replicate A true) [])
      tag present found selected source payload alphabet (List.replicate A true))
    checkerRegisters_injective checkerStacks_injective ht
  refine ⟨n,hn,r,?_⟩
  simpa only [checker,embed_wide] using he

end SubexponentialSAT.Subexp.CoefficientSearchProgram

end OAI.Algorithms
