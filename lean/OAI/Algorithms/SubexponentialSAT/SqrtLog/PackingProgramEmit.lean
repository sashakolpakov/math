import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram

namespace OAI.Algorithms

/-! Fixed serialization primitives for weighted candidate-score streams. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 8 12

def reg (i : Fin 3) : Fin 8 := i.castAdd 5
def low (i : Fin 8) : Fin 12 := i.castAdd 4
def writerStack : Fin 2 → Fin 12 := ![4,9]

theorem reg_injective : Function.Injective reg := Fin.castAdd_injective _ _
theorem low_injective : Function.Injective low := Fin.castAdd_injective _ _
theorem writerStack_injective : Function.Injective writerStack := by decide

abbrev writeEscaped : Cmd 8 12 := .call
  (SubexponentialSAT.ProgramLinking.liftProgram CandidateScoreProgram.reverseEscapeProgram reg writerStack)

def writerLocal (d : Data) : State 3 2 :=
  CandidateScoreProgram.writerData false false true []
    ((TupleProgram.escaped (d.stacks 4)).reverse ++ d.stacks 9)

 theorem writeEscaped_eval (d : Data) :
    Eval writeEscaped (4*(d.stacks 4).length+4) d
      (embedState reg writerStack d (writerLocal d)) := by
  have h := CandidateScoreProgram.reverseEscape_trace (d.stacks 4) (d.stacks 9)
    (d.regs (reg 0)) (d.regs (reg 1)) (d.regs (reg 2))
  apply eval_call_from_state _ reg writerStack d reg_injective writerStack_injective
  have hp : projectState reg writerStack d = CandidateScoreProgram.writerData
      (d.regs (reg 0)) (d.regs (reg 1)) (d.regs (reg 2)) (d.stacks 4) (d.stacks 9) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> funext j <;> fin_cases j <;> rfl
  rw [hp]
  exact h

 def emit : Cmd 8 12 := .seq (TupleProgram.pushConst 9 0 true)
  (.seq writeEscaped (TupleProgram.pushConst 9 0 false))

 theorem emit_eval (d : Data) :
    ∃ e : Data, Eval emit (4*(d.stacks 4).length+8) d e ∧
      e.stacks 4 = [] ∧
      e.stacks 9 = CandidateScoreProgram.reverseRecord (d.stacks 4) (d.stacks 9) ∧
      (∀ j, j ≠ 4 → j ≠ 9 → e.stacks j = d.stacks j) := by
  let a := TupleProgram.pushedState 9 0 true d
  let b := embedState reg writerStack a (writerLocal a)
  let e := TupleProgram.pushedState 9 0 false b
  have hrun := (TupleProgram.pushConst_eval 9 0 true d).seq
    ((writeEscaped_eval a).seq (TupleProgram.pushConst_eval 9 0 false b))
  have hb4 : b.stacks 4 = [] :=
    embedState_stack reg writerStack a (writerLocal a) writerStack_injective 0
  have hb9 : b.stacks 9 = (TupleProgram.escaped (d.stacks 4)).reverse ++ true :: d.stacks 9 := by
    exact embedState_stack reg writerStack a (writerLocal a) writerStack_injective 1
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · convert hrun using 1 <;> simp [a, emit ] ; omega
  · simpa [e, TupleProgram.pushedState] using hb4
  · simp [e, hb9, CandidateScoreProgram.reverseRecord,
      TupleProgram.frame_eq_escaped, List.reverse_append, List.append_assoc]
  · intro j hj4 hj9
    have hj : ¬∃ i, writerStack i = j := by
      rintro ⟨i, rfl⟩
      fin_cases i <;> simp [writerStack] at hj4 hj9
    have h := embedState_stack_frame reg writerStack a (writerLocal a) j hj
    simpa [e, b, a, TupleProgram.pushedState, hj9] using h

end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
