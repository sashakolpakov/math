import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Preserving complemented-literal queries

The clause iterator supplies a literal's unary word in reverse order. This
fixed program preserves that query on stack 0 and writes the reversed unary
word for the opposite literal on stack 1. Stacks 2 and 3 are empty workspaces
on entry and return. All costs below count actual finite-program transitions.
-/

namespace SubexponentialSAT.SubexpNegatedQueryProgram

open BitProgram StructuredCalls
open ParserProgram (pair)

/-- The four ports are original query, result, work, and scratch. -/
def slots (query result work scratch : List Bool) : Fin 4 → List Bool :=
  fun i => if i = 0 then query else if i = 1 then result else if i = 2 then work else scratch

@[simp] theorem slots_zero (a b c d : List Bool) : slots a b c d 0 = a := rfl
@[simp] theorem slots_one (a b c d : List Bool) : slots a b c d 1 = b := rfl
@[simp] theorem slots_two (a b c d : List Bool) : slots a b c d 2 = c := rfl
@[simp] theorem slots_three (a b c d : List Bool) : slots a b c d 3 = d := rfl

@[simp] theorem update_slots_one (a b c d e : List Bool) :
    Function.update (slots a b c d) 1 e = slots a e c d := by
  funext i
  fin_cases i <;> simp [slots]

@[simp] theorem update_slots_two (a b c d e : List Bool) :
    Function.update (slots a b c d) 2 e = slots a b e d := by
  funext i
  fin_cases i <;> simp [slots]

abbrev state (value present : Bool) (query result work scratch : List Bool) : State 2 4 :=
  ⟨pair value present, slots query result work scratch⟩

abbrev copyQuery : Program 2 4 8 := StackRoutines.copyProgram 0 2 3 0 1
abbrev reverseWork : Program 2 4 10 := StackRoutines.reverseProgram 2 1 3 0 1
abbrev reverseResult : Program 2 4 10 := StackRoutines.reverseProgram 1 2 3 0 1

/-- Only the work and result ports are assigned to the unary complementer. -/
def negatePorts (i : Fin 2) : Fin 4 := if i = 0 then 2 else 1

theorem negatePorts_injective : Function.Injective negatePorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [negatePorts] at h ⊢

abbrev negateWork : Program 2 4 15 :=
  ProgramLinking.liftProgram SubexpNormalizeProgram.negateProgram id negatePorts

/-- The syntax, register count, stack count, and label count are independent
of the encoded literal's value. -/
abbrev command : Cmd 2 4 :=
  .seq (.call copyQuery)
    (.seq (.call reverseWork) (.seq (.call negateWork) (.call reverseResult)))

abbrev program := compiled command 0 1

theorem copyQuery_eval (query : List Bool) (v p : Bool) :
    Eval (.call copyQuery) (7 * query.length + 5)
      (state v p query [] [] []) (state false false query [] query []) := by
  have h := StackRoutines.copyProgram_trace (0 : Fin 4) 2 3 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (pair v p) (slots query [] [] []) rfl
  have hh := StackRoutines.halt_after_trace copyQuery h 7 rfl rfl
  apply Eval.call
  simpa [copyQuery, StackRoutines.copyResult, StackRoutines.copyStacks,
    readRegs, state, StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem reverseWork_eval (query work : List Bool) (v p : Bool) :
    Eval (.call reverseWork) (9 * work.length + 7)
      (state v p query [] work []) (state false false query [] work.reverse []) := by
  have h := StackRoutines.reverseProgram_trace (2 : Fin 4) 1 3 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (pair v p) (slots query [] work []) rfl rfl
  have hh := StackRoutines.halt_after_trace reverseWork h 9 rfl rfl
  apply Eval.call
  simpa [reverseWork, StackRoutines.reverseResult, StackRoutines.reverseStacks,
    readRegs, state, StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem reverseResult_eval (query result : List Bool) (v p : Bool) :
    Eval (.call reverseResult) (9 * result.length + 7)
      (state v p query result [] []) (state false false query result.reverse [] []) := by
  have h := StackRoutines.reverseProgram_trace (1 : Fin 4) 2 3 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (pair v p) (slots query result [] []) rfl rfl
  have hh := StackRoutines.halt_after_trace reverseResult h 9 rfl rfl
  apply Eval.call
  simpa [reverseResult, StackRoutines.reverseResult, StackRoutines.reverseStacks,
    readRegs, state, StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem extend_negate_slots (query input output : List Bool) :
    Function.extend negatePorts (pair input output) (slots query [] [] []) =
      slots query output input [] := by
  funext i
  fin_cases i
  · apply Function.extend_apply'
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [negatePorts] at hj
  · exact negatePorts_injective.extend_apply _ _ 1
  · exact negatePorts_injective.extend_apply _ _ 0
  · apply Function.extend_apply'
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [negatePorts] at hj

theorem embed_negate_state (query input output : List Bool) (v p : Bool) :
    embedState id negatePorts (state false false query [] [] [])
      ⟨pair v p, pair input output⟩ = state v p query output input [] := by
  simp [embedState, state, extend_negate_slots]

theorem negateWork_eval (c : ℕ) (query : List Bool) (v p : Bool) :
    Eval (.call negateWork) (SubexpNormalizeProgram.negateSteps c)
      (state v p query [] (Encoding.encodeNat c) [])
      (state false false query (Encoding.encodeNat (SubexpFrontend.negateCode c)) [] []) := by
  have h : Trace SubexpNormalizeProgram.negateProgram
      (SubexpNormalizeProgram.negateSteps c)
      ((⟨pair v p, pair (Encoding.encodeNat c) []⟩ : State 2 2).withPC
        (some SubexpNormalizeProgram.negateProgram.entry))
      ((⟨pair false false, pair [] (Encoding.encodeNat (SubexpFrontend.negateCode c))⟩ :
        State 2 2).withPC none) := by
    simpa [StructuredProgram.State.withPC, SubexpNormalizeProgram.negateProgram,
      ParserProgram.cfg] using SubexpNormalizeProgram.negate_trace c [] [] v p
  have he := eval_call_lifted SubexpNormalizeProgram.negateProgram id negatePorts
    (state false false query [] [] []) Function.injective_id negatePorts_injective h
  simpa only [embed_negate_state, negateWork] using he

/-- Exact complete execution count, including the final halt. -/
def steps (c : ℕ) : ℕ :=
  16 * (Encoding.encodeNat c).length +
    9 * (Encoding.encodeNat (SubexpFrontend.negateCode c)).length +
    SubexpNormalizeProgram.negateSteps c + 20

theorem command_eval (c : ℕ) (v p : Bool) :
    Eval command (steps c - 1)
      (state v p (Encoding.encodeNat c).reverse [] [] [])
      (state false false (Encoding.encodeNat c).reverse
        (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse [] []) := by
  have hcopy := copyQuery_eval (Encoding.encodeNat c).reverse v p
  have hrev := reverseWork_eval (Encoding.encodeNat c).reverse
    (Encoding.encodeNat c).reverse false false
  simp only [List.reverse_reverse, List.length_reverse] at hcopy hrev
  have hneg := negateWork_eval c (Encoding.encodeNat c).reverse false false
  have hout := reverseResult_eval (Encoding.encodeNat c).reverse
    (Encoding.encodeNat (SubexpFrontend.negateCode c)) false false
  have h := Eval.seq hcopy (Eval.seq hrev (Eval.seq hneg hout))
  convert h using 1
  simp only [ steps]
  omega

theorem program_trace (c : ℕ) (v p : Bool) :
    Trace program (steps c)
      ((state v p (Encoding.encodeNat c).reverse [] [] []).withPC (some program.entry))
      ((state false false (Encoding.encodeNat c).reverse
        (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse [] []).withPC none) := by
  have h := compiled_halt_trace (command_eval c v p) 0 1
  have hs : steps c - 1 + 1 = steps c := by unfold steps; omega
  simpa only [hs, program] using h

theorem negateCode_le (c : ℕ) : SubexpFrontend.negateCode c ≤ c + 1 := by
  unfold SubexpFrontend.negateCode
  split <;> omega

theorem steps_le (c : ℕ) : steps c ≤ 29 * (Encoding.encodeNat c).length + 35 := by
  have hn := negateCode_le c
  have hs := SubexpNormalizeProgram.negateSteps_le c
  simp only [steps, Encoding.length_encodeNat]
  omega

/-- Linear time in the actual query's bit length; the original query remains
available to the caller and both work stacks are empty on return. -/
theorem program_runsIn (c : ℕ) (v p : Bool) :
    RunsIn program (29 * (Encoding.encodeNat c).length + 35)
      ((state v p (Encoding.encodeNat c).reverse [] [] []).withPC (some program.entry))
      ((state false false (Encoding.encodeNat c).reverse
        (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse [] []).withPC none) :=
  ⟨steps c, steps_le c, program_trace c v p⟩

theorem initial_eq (query : List Bool) :
    initial program query = (state false false query [] [] []).withPC (some program.entry) := by
  simp only [initial, StructuredProgram.State.withPC]
  congr 1
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem raw_input_trace (c : ℕ) :
    Trace program (steps c) (initial program (Encoding.encodeNat c).reverse)
      ((state false false (Encoding.encodeNat c).reverse
        (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse [] []).withPC none) := by
  rw [initial_eq]
  exact program_trace c false false

theorem literal_trace {n : ℕ} (l : SAT.Literal (Fin n)) (v p : Bool) :
    Trace program (steps (Encoding.literalCode l))
      ((state v p (Encoding.encodeNat (Encoding.literalCode l)).reverse [] [] []).withPC
        (some program.entry))
      ((state false false (Encoding.encodeNat (Encoding.literalCode l)).reverse
        (Encoding.encodeNat (Encoding.literalCode l.negate)).reverse [] []).withPC none) := by
  rw [SubexpFrontend.literalCode_negate]
  exact program_trace _ v p

/-- The proved source trace compiles to actual primitive-tape execution. -/
theorem primitive_execution (c : ℕ) (v p : Bool) :
    Computation.RunsIn (primitive program).step (primitiveOverhead program * steps c)
      (primitiveCfg program
        ((state v p (Encoding.encodeNat c).reverse [] [] []).withPC (some program.entry)))
      (primitiveCfg program
        ((state false false (Encoding.encodeNat c).reverse
          (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse [] []).withPC none)) :=
  primitive_trace program (program_trace c v p)

theorem raw_input_primitive (c : ℕ) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (29 * (Encoding.encodeNat c).length + 35))
      ((primitive program).init (Encoding.encodeNat c).reverse)
      (primitiveCfg program
        ((state false false (Encoding.encodeNat c).reverse
          (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse [] []).withPC none)) := by
  have h := (primitive_trace program (raw_input_trace c)).mono
    (Nat.mul_le_mul_left (primitiveOverhead program) (steps_le c))
  simpa only [primitive_initial] using h

end SubexponentialSAT.SubexpNegatedQueryProgram

end OAI.Algorithms
