import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFullShapeProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Preserving capture of the padded-array shape

The actual unary chunk count is copied before the shape constructor consumes
its working counter. The width and count masters are preserved, as is every
caller stack except the initially empty output. All three work stacks are
restored empty. Port maps are fixed parts of the finite program.
-/

namespace SubexponentialSAT.SubexpFullShapeCapture

open BitProgram StructuredCalls

abbrev Data (R S : ℕ) := StructuredProgram.State R S

/-- Local ports: width 0, output 1, shape scratch 2, count master 3,
working count 4, and copy scratch 5. -/
def shapeIndices : Fin 4 → Fin 6 := ![0, 1, 2, 4]

theorem shapeIndices_injective : Function.Injective shapeIndices := by decide

def shapePorts {S : ℕ} (stack : Fin 6 ↪ Fin S) : Fin 4 → Fin S :=
  stack ∘ shapeIndices

theorem shapePorts_injective {S : ℕ} (stack : Fin 6 ↪ Fin S) :
    Function.Injective (shapePorts stack) :=
  stack.injective.comp shapeIndices_injective

def resetRegs {R : ℕ} (register : Fin 3 ↪ Fin R) (regs : Fin R → Bool) :
    Fin R → Bool :=
  Function.update (Function.update (Function.update regs (register 0) false)
    (register 1) false) (register 2) false

@[simp] theorem resetRegs_port {R : ℕ} (register : Fin 3 ↪ Fin R)
    (regs : Fin R → Bool) (i : Fin 3) :
    resetRegs register regs (register i) = false := by
  fin_cases i <;> simp [resetRegs, register.injective.eq_iff]

theorem resetRegs_frame {R : ℕ} (register : Fin 3 ↪ Fin R)
    (regs : Fin R → Bool) (i : Fin R) (hi : ¬ ∃ j, register j = i) :
    resetRegs register regs i = regs i := by
  have h0 : i ≠ register 0 := fun h => hi ⟨0, h.symm⟩
  have h1 : i ≠ register 1 := fun h => hi ⟨1, h.symm⟩
  have h2 : i ≠ register 2 := fun h => hi ⟨2, h.symm⟩
  simp [resetRegs, h0, h1, h2]

def copied {R S : ℕ} (register : Fin 3 ↪ Fin R) (stack : Fin 6 ↪ Fin S)
    (d : Data R S) (D : ℕ) : Data R S :=
  ⟨readRegs d.regs (register 0) (register 1) none,
    Function.update d.stacks (stack 4) (List.replicate D true)⟩

def ready {R S : ℕ} (register : Fin 3 ↪ Fin R) (stack : Fin 6 ↪ Fin S)
    (d : Data R S) (D : ℕ) : Data R S :=
  ⟨resetRegs register d.regs,
    Function.update d.stacks (stack 4) (List.replicate D true)⟩

/-- Only the output stack changes; the three selected Boolean registers end
false, while all other caller registers are preserved. -/
def output {R S : ℕ} (register : Fin 3 ↪ Fin R) (stack : Fin 6 ↪ Fin S)
    (d : Data R S) (D : ℕ) : Data R S :=
  ⟨resetRegs register d.regs,
    Function.update d.stacks (stack 1)
      (SubexpFullShapeProgram.fullShape D (d.stacks (stack 0)))⟩

abbrev copyCount {R S : ℕ} (register : Fin 3 ↪ Fin R) (stack : Fin 6 ↪ Fin S) :
    Cmd R S :=
  .call (StackRoutines.copyProgram (stack 3) (stack 4) (stack 5)
    (register 0) (register 1))

abbrev resetActive {R S : ℕ} (register : Fin 3 ↪ Fin R) : Cmd R S :=
  .base (.atom (.set (register 2) false))

abbrev makeShape {R S : ℕ} (register : Fin 3 ↪ Fin R) (stack : Fin 6 ↪ Fin S) :
    Cmd R S :=
  .call (ProgramLinking.liftProgram SubexpFullShapeProgram.program
    register (shapePorts stack))

abbrev command {R S : ℕ} (register : Fin 3 ↪ Fin R) (stack : Fin 6 ↪ Fin S) :
    Cmd R S :=
  .seq (copyCount register stack) (.seq (resetActive register) (makeShape register stack))

abbrev program {R S : ℕ} (register : Fin 3 ↪ Fin R) (stack : Fin 6 ↪ Fin S) :
    Program R S (size (command register stack) + 1) :=
  compiled (command register stack) (stack 3) (stack 1)

@[simp] theorem program_labels {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) : size (command register stack) + 1 = 22 := rfl

abbrev localProgram : Program 3 6 22 :=
  program (Function.Embedding.refl _) (Function.Embedding.refl _)

theorem copyCount_eval {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) (d : Data R S) (D : ℕ)
    (hD : d.stacks (stack 3) = List.replicate D true)
    (h4 : d.stacks (stack 4) = []) (h5 : d.stacks (stack 5) = []) :
    Eval (copyCount register stack) (7 * D + 5) d (copied register stack d D) := by
  have h := ListRegisterProgram.copy_run (stack 3) (stack 4) (stack 5)
    (register 0) (register 1)
    (by simp [stack.injective.eq_iff]) (by simp [stack.injective.eq_iff])
    (by simp [stack.injective.eq_iff]) (by simp [register.injective.eq_iff])
    d.regs d.stacks h5
  apply Eval.call
  simpa only [copied, ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, hD, h4, List.append_nil, List.length_replicate] using h

theorem resetActive_eval {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) (d : Data R S) (D : ℕ) :
    Eval (resetActive register) 1 (copied register stack d D) (ready register stack d D) := by
  exact .base (.atom _ _)

private theorem embed_ready {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) (d : Data R S) (D : ℕ)
    (h1 : d.stacks (stack 1) = []) (h2 : d.stacks (stack 2) = []) :
    embedState register (shapePorts stack) (ready register stack d D)
      (SubexpFullShapeProgram.inputState D (d.stacks (stack 0))) =
      ready register stack d D := by
  apply embedState_eq_of_ports _ _ _ _ _ register.injective (shapePorts_injective stack)
  · intro i; fin_cases i <;> exact resetRegs_port register d.regs _
  · intro i hi; rfl
  · intro i
    fin_cases i <;>
      simp [ready, shapePorts, shapeIndices, SubexpFullShapeProgram.inputState,
        Subexp.BlockCopyProgram.initialState, Subexp.BlockCopyProgram.data,
        stack.injective.eq_iff, h1, h2]
  · intro i hi; rfl

private theorem embed_output {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) (d : Data R S) (D : ℕ)
    (h2 : d.stacks (stack 2) = []) (h4 : d.stacks (stack 4) = []) :
    embedState register (shapePorts stack) (ready register stack d D)
      (SubexpFullShapeProgram.outputState D (d.stacks (stack 0))) =
      output register stack d D := by
  apply embedState_eq_of_ports _ _ _ _ _ register.injective (shapePorts_injective stack)
  · intro i; fin_cases i <;> exact resetRegs_port register d.regs _
  · intro i hi; rfl
  · intro i
    fin_cases i <;>
      simp [output, shapePorts, shapeIndices, SubexpFullShapeProgram.outputState,
        Subexp.BlockCopyProgram.data, stack.injective.eq_iff, h2, h4]
  · intro i hi
    have h1 : i ≠ stack 1 := fun h => hi ⟨1, h.symm⟩
    have h4' : i ≠ stack 4 := fun h => hi ⟨3, h.symm⟩
    simp [output, ready, h1, h4']

/-- Actual execution from an arbitrary caller state. The unary count comes
from a physical master stack; it is copied and is not consumed. -/
theorem command_eval {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) (d : Data R S) (D : ℕ)
    (hD : d.stacks (stack 3) = List.replicate D true)
    (h1 : d.stacks (stack 1) = []) (h2 : d.stacks (stack 2) = [])
    (h4 : d.stacks (stack 4) = []) (h5 : d.stacks (stack 5) = []) :
    Eval (command register stack) (D * (7 * (d.stacks (stack 0)).length + 14) + 9)
      d (output register stack d D) := by
  have hs := SubexpFullShapeProgram.lifted_eval register (shapePorts stack)
    register.injective (shapePorts_injective stack) (ready register stack d D)
    D (d.stacks (stack 0))
  rw [embed_ready register stack d D h1 h2, embed_output register stack d D h2 h4] at hs
  have h := Eval.seq (copyCount_eval register stack d D hD h4 h5)
    (Eval.seq (resetActive_eval register stack d D) hs)
  have hc : 7 * D + 5 + (1 + (D * (7 * (d.stacks (stack 0)).length + 7) + 3)) =
      D * (7 * (d.stacks (stack 0)).length + 14) + 9 := by ring
  simpa only [command, makeShape, hc] using h

theorem trace {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) (d : Data R S) (D : ℕ)
    (hD : d.stacks (stack 3) = List.replicate D true)
    (h1 : d.stacks (stack 1) = []) (h2 : d.stacks (stack 2) = [])
    (h4 : d.stacks (stack 4) = []) (h5 : d.stacks (stack 5) = []) :
    Trace (program register stack) (D * (7 * (d.stacks (stack 0)).length + 14) + 10)
      (d.withPC (some (program register stack).entry))
      ((output register stack d D).withPC none) := by
  simpa only [program, Nat.add_assoc] using
    compiled_halt_trace (command_eval register stack d D hD h1 h2 h4 h5) (stack 3) (stack 1)

theorem caller_eval {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) (d : Data R S) (D : ℕ)
    (hD : d.stacks (stack 3) = List.replicate D true)
    (h1 : d.stacks (stack 1) = []) (h2 : d.stacks (stack 2) = [])
    (h4 : d.stacks (stack 4) = []) (h5 : d.stacks (stack 5) = []) :
    Eval (.call (program register stack)) (D * (7 * (d.stacks (stack 0)).length + 14) + 10)
      d (output register stack d D) :=
  .call _ (trace register stack d D hD h1 h2 h4 h5)

@[simp] theorem output_shape_length {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) (d : Data R S) (D : ℕ) :
    ((output register stack d D).stacks (stack 1)).length =
      D * (d.stacks (stack 0)).length := by
  simp [output]

theorem output_stack_preserved {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) (d : Data R S) (D : ℕ) (i : Fin S) (hi : i ≠ stack 1) :
    (output register stack d D).stacks i = d.stacks i := by
  simp [output, hi]

theorem primitive_execution {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (stack : Fin 6 ↪ Fin S) (d : Data R S) (D : ℕ)
    (hD : d.stacks (stack 3) = List.replicate D true)
    (h1 : d.stacks (stack 1) = []) (h2 : d.stacks (stack 2) = [])
    (h4 : d.stacks (stack 4) = []) (h5 : d.stacks (stack 5) = []) :
    Computation.RunsIn (primitive (program register stack)).step
      (primitiveOverhead (program register stack) *
        (D * (7 * (d.stacks (stack 0)).length + 14) + 10))
      (primitiveCfg (program register stack) (d.withPC (some (program register stack).entry)))
      (primitiveCfg (program register stack) ((output register stack d D).withPC none)) :=
  primitive_trace _ (trace register stack d D hD h1 h2 h4 h5)

end SubexponentialSAT.SubexpFullShapeCapture

end OAI.Algorithms
