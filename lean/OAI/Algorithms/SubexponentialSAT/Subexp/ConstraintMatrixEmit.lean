import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssembly
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! A fixed framing subroutine for the actual constraint-matrix emitter.
The source scalar is preserved and its reversed frame is prepended to the
reversed matrix accumulator. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixEmit

open BitProgram StructuredCalls

abbrev Data := State 3 3

def state (regs : Fin 3 → Bool) (payload accumulator : List Bool) : Data :=
  ⟨regs, SubexpHornerProgram.triple payload accumulator []⟩

def resultRegs : Fin 3 → Bool := SubexpHornerProgram.triple false false true

abbrev command : Cmd 3 3 := .seq (.base (.atom (.set 2 true)))
  (.call SubexpBlockAssembly.frameBody)

def program := compiled command 0 1

theorem command_eval (regs : Fin 3 → Bool) (payload accumulator : List Bool) :
    Eval command (8 * payload.length + 7) (state regs payload accumulator)
      (state resultRegs payload ((Encoding.frame payload).reverse ++ accumulator)) := by
  let middle := state (Function.update regs 2 true) payload accumulator
  have hset : Eval (.base (.atom (.set 2 true))) 1
      (state regs payload accumulator) middle := by
    simpa [middle, state, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using
      Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (s := 3) 2 true)
        (state regs payload accumulator))
  have hr : Function.update regs 2 true =
      SubexpHornerProgram.triple (regs 0) (regs 1) true := by
    funext j
    fin_cases j <;> simp [SubexpHornerProgram.triple]
  have hcall : Eval (.call SubexpBlockAssembly.frameBody) (8 * payload.length + 6)
      middle (state resultRegs payload ((Encoding.frame payload).reverse ++ accumulator)) := by
    apply Eval.call
    simpa [middle, state, resultRegs, hr, SubexpHornerProgram.Literal.cfg,
      StructuredProgram.State.withPC, SubexpBlockAssembly.frameBody] using
      SubexpBlockAssembly.frameBody_trace payload accumulator (regs 0) (regs 1)
  have h := hset.seq hcall
  have hcost : 1 + (8 * payload.length + 6) = 8 * payload.length + 7 := by omega
  rw [hcost] at h
  exact h

theorem program_trace (regs : Fin 3 → Bool) (payload accumulator : List Bool) :
    Trace program (8 * payload.length + 8)
      ((state regs payload accumulator).withPC (some program.entry))
      ((state resultRegs payload ((Encoding.frame payload).reverse ++ accumulator)).withPC none) := by
  simpa only [program, Nat.add_assoc] using compiled_halt_trace
    (command_eval regs payload accumulator) 0 1

abbrev call {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 3 → Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram program register stack)

noncomputable def after {R S : ℕ} (register : Fin 3 → Fin R)
    (stack : Fin 3 → Fin S) (a : State R S) : State R S :=
  ⟨Function.extend register resultRegs a.regs,
    Function.update a.stacks (stack 1)
      ((Encoding.frame (a.stacks (stack 0))).reverse ++ a.stacks (stack 1))⟩

theorem call_eval {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 3 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (a : State R S) (h2 : a.stacks (stack 2) = []) :
    Eval (call register stack) (8 * (a.stacks (stack 0)).length + 8)
      a (after register stack a) := by
  have hstart : state (a.regs ∘ register) (a.stacks (stack 0)) (a.stacks (stack 1)) =
      projectState register stack a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [SubexpHornerProgram.triple, h2]
  have ht := program_trace (a.regs ∘ register) (a.stacks (stack 0)) (a.stacks (stack 1))
  rw [hstart] at ht
  have he := eval_call_from_state program register stack a hr hs ht
  have hlocal :
      (state resultRegs (a.stacks (stack 0))
        ((Encoding.frame (a.stacks (stack 0))).reverse ++ a.stacks (stack 1))).stacks =
      Function.update (projectState register stack a).stacks 1
        ((Encoding.frame (a.stacks (stack 0))).reverse ++ a.stacks (stack 1)) := by
    funext j
    fin_cases j <;> simp [state, projectState, SubexpHornerProgram.triple, h2]
  have hbase : Function.extend stack (projectState register stack a).stacks a.stacks =
      a.stacks := congrArg StructuredProgram.State.stacks (embedState_project register stack a hr hs)
  have hend : embedState register stack a
      (state resultRegs (a.stacks (stack 0))
        ((Encoding.frame (a.stacks (stack 0))).reverse ++ a.stacks (stack 1))) =
      after register stack a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [hlocal, ProgramLinking.extend_update hs, hbase]
  rw [hend] at he
  exact he

theorem after_register_frame {R S : ℕ} (register : Fin 3 → Fin R)
    (stack : Fin 3 → Fin S) (a : State R S) (j : Fin R)
    (hj : ¬ ∃ k, register k = j) :
    (after register stack a).regs j = a.regs j :=
  Function.extend_apply' _ _ _ hj

end SubexponentialSAT.Subexp.ConstraintMatrixEmit

end OAI.Algorithms
