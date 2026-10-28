import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! Fixed unary-counter and record-emission instructions for incidence plans. -/
namespace SubexponentialSAT.SubexpIncidencePlanPrimitives

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 10 10

abbrev increment (dst : Fin 10) : Cmd 10 10 :=
  .seq (.base (.atom (.set 0 true))) (.base (.atom (.push dst 0)))

def incremented (dst : Fin 10) (d : Data) : Data :=
  ⟨Function.update d.regs 0 true, Function.update d.stacks dst (true :: d.stacks dst)⟩

theorem increment_eval (dst : Fin 10) (d : Data) :
    Eval (increment dst) 2 d (incremented dst d) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) true) d)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 10)) _))
  simpa [increment, incremented, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

abbrev copy (src dst tmp : Fin 10) : Cmd 10 10 :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

def copied (src dst : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst tmp : Fin 10) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (ht : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d (copied src dst d) :=
  .call _ (ListRegisterProgram.copy_run src dst tmp 0 1 hsd hst htd (by decide)
    d.regs d.stacks ht)

def emitReg : Fin 3 → Fin 10 := ![0, 1, 4]
def emitStack : Fin 4 → Fin 10 := ![6, 3, 7, 1]

theorem emitReg_injective : Function.Injective emitReg := by decide
theorem emitStack_injective : Function.Injective emitStack := by decide

abbrev emit : Cmd 10 10 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack)

def emitted (selected : Bool) (bits : List Bool) (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 true) 4 false,
    Function.update (Function.update d.stacks 1 []) 7
      (if selected then true :: (Encoding.frame bits ++ d.stacks 7) else d.stacks 7)⟩

/-- Emit the supplied unary index exactly when the actual membership flag
is set. The framed list is accumulated in reverse encounter order. -/
theorem emit_eval (selected : Bool) (bits : List Bool) (d : Data)
    (hp : d.stacks 1 = bits.reverse) (hf : d.regs 4 = selected) :
    Eval emit (SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1)
      d (emitted selected bits d) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) selected
    (d.stacks 6) (d.stacks 3) (d.stacks 7) bits.reverse
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 6) (d.stacks 3)
    (if selected then true :: (Encoding.frame bits ++ d.stacks 7) else d.stacks 7) []
  have ha : embedState emitReg emitStack d a = d := by
    apply embedState_eq_of_ports emitReg emitStack d d a emitReg_injective emitStack_injective
    · intro i
      fin_cases i <;> simp [a, emitReg, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.triple, hf]
    · intros; rfl
    · intro i
      fin_cases i <;> simp [a, emitStack, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hp]
    · intros; rfl
  have hb : embedState emitReg emitStack d b = emitted selected bits d := by
    apply embedState_eq_of_ports emitReg emitStack d (emitted selected bits d) b
      emitReg_injective emitStack_injective
    · intro i
      fin_cases i <;> simp [b, emitReg, emitted, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.triple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨2, h.symm⟩
      simp [emitted, h0, h1, h4]
    · intro i
      fin_cases i <;> simp [b, emitStack, emitted, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨3, h.symm⟩
      have h7 : i ≠ 7 := fun h => hi ⟨2, h.symm⟩
      simp [emitted, h1, h7]
  have h := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack d
    emitReg_injective emitStack_injective
    (SubexpNormalizeProgram.emitIfSelected_trace selected bits
      (d.stacks 6) (d.stacks 3) (d.stacks 7) (d.regs 0) (d.regs 1))
  change Eval emit _ (embedState emitReg emitStack d a) (embedState emitReg emitStack d b) at h
  simpa only [ha, hb] using h

theorem emit_cost (selected : Bool) (bits : List Bool) :
    SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1 ≤ 5 * bits.length + 12 :=
  SubexpNormalizeProgram.emitIfSelected_steps_le selected bits

end SubexponentialSAT.SubexpIncidencePlanPrimitives

end OAI.Algorithms
