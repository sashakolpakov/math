import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

def projectState {r s R S : ℕ} (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (d : State R S) : State r s := ⟨d.regs ∘ register, d.stacks ∘ stack⟩

@[simp] theorem embedState_project {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (d : State R S)
    (hr : Function.Injective register) (hs : Function.Injective stack) :
    embedState register stack d (projectState register stack d) = d := by
  apply embedState_eq_of_ports register stack d d _ hr hs
  · intro i; rfl
  · intro i hi; rfl
  · intro i; rfl
  · intro i hi; rfl

@[simp] theorem projectState_embed {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack) :
    projectState register stack (embedState register stack frame d) = d := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    exact embedState_register register stack frame d hr i
  · funext i
    exact embedState_stack register stack frame d hs i

/-- A complete local run can be called directly from an arbitrary caller state. -/
theorem eval_call_from_state {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (d : State R S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    {n : ℕ} {b : State r s}
    (h : Trace p n ((projectState register stack d).withPC (some p.entry)) (b.withPC none)) :
    Eval (.call (ProgramLinking.liftProgram p register stack)) n
      d (embedState register stack d b) := by
  simpa only [embedState_project register stack d hr hs] using
    eval_call_lifted p register stack d hr hs h

/-- One stack update in the local result becomes the same update at its
assigned caller port. This is an equality of state descriptions. -/
theorem embedState_update_stack {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) (hs : Function.Injective stack)
    (k : Fin s) (word : List Bool) :
    embedState register stack frame { d with «stacks» := Function.update d.stacks k word } =
      { embedState register stack frame d with
        «stacks» := Function.update (embedState register stack frame d).stacks (stack k) word } := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · exact ProgramLinking.extend_update hs d.stacks frame.stacks k word

theorem embedState_update_register {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) (hr : Function.Injective register)
    (k : Fin r) (value : Bool) :
    embedState register stack frame { d with regs := Function.update d.regs k value } =
      { embedState register stack frame d with
        regs := Function.update (embedState register stack frame d).regs (register k) value } := by
  apply congrArg₂ StructuredProgram.State.mk
  · exact ProgramLinking.extend_update hr d.regs frame.regs k value
  · rfl

/-- Lift any fixed structured command by compiling and calling its finite
instruction table. The extra source instruction is its final return. -/
abbrev liftCommand {r s R S : ℕ} (c : Cmd r s) (inputStack outputStack : Fin s)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram (compiled c inputStack outputStack) register stack)

theorem eval_liftCommand {r s R S : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (frame : State R S)
    (hr : Function.Injective register) (hs : Function.Injective stack) :
    Eval (liftCommand c inputStack outputStack register stack) (n + 1)
      (embedState register stack frame a) (embedState register stack frame b) :=
  eval_call_lifted (compiled c inputStack outputStack) register stack frame hr hs
    (compiled_halt_trace h inputStack outputStack)

theorem eval_liftCommand_from_state {r s R S : ℕ}
    (c : Cmd r s) (inputStack outputStack : Fin s)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (d : State R S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    {n : ℕ} {b : State r s} (h : Eval c n (projectState register stack d) b) :
    Eval (liftCommand c inputStack outputStack register stack) (n + 1)
      d (embedState register stack d b) := by
  simpa only [embedState_project register stack d hr hs] using
    eval_liftCommand h inputStack outputStack register stack d hr hs

/-- Different finite execution derivations of the same structured command
must have the same final data. The existing source port supplies a concrete
compiled machine, and determinism is inherited from its actual transition. -/
theorem Eval.final_unique {r s : ℕ} (port : Fin s) {c : Cmd r s}
    {n m : ℕ} {a b d : State r s} (h : Eval c n a b) (g : Eval c m a d) : b = d := by
  have hb := compiled_halt_trace h port port
  have hd := compiled_halt_trace g port port
  have heq := Computation.RunsIn.terminal_unique
    (show RunsIn (compiled c port port) (n + 1)
      (a.withPC (some (compiled c port port).entry)) (b.withPC none) from
      ⟨n + 1, le_rfl, hb⟩)
    (show RunsIn (compiled c port port) (m + 1)
      (a.withPC (some (compiled c port port).entry)) (d.withPC none) from
      ⟨m + 1, le_rfl, hd⟩)
    (by simp [step, StructuredProgram.State.withPC])
    (by simp [step, StructuredProgram.State.withPC])
  exact congrArg StructuredProgram.State.ofCfg heq

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
