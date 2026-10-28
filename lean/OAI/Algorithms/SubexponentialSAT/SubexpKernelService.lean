import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpKernelControl
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Source construction inside the retained-moment loop

This is an actual finite service on the job emitter's 24-stack frame. It
constructs the source from encoded blocks, moves the forward result to the
captured-source port, and preserves the exponent, dimensions, and jobs already
emitted. The mathematical state definitions below describe storage only; the
executable service consists of fixed instruction tables and Boolean writes.
-/

namespace SubexponentialSAT.SubexpKernelService

open BitProgram StructuredCalls
open SubexpKernelControl (Word Block encodeBlocks momentCode)

abbrev Data := State 3 24
abbrev Code := Cmd 3 24

def kernelPorts : Fin 8 → Fin 24 := ![20, 18, 19, 21, 22, 23, 16, 17]

theorem kernelPorts_injective : Function.Injective kernelPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [kernelPorts]

/-- Ports 0,2,3,14 are the moment loop's exponent, dimensions, and job output.
All other ports outside the explicitly assigned workspace are framed too. -/
def state (frame : Data) (regs : Fin 3 → Bool)
    (source zero one captured temporary : Word) : Data where
  regs := regs
  «stacks» := fun i =>
    if i = 20 then source else if i = 18 then zero else if i = 19 then one
    else if i = 1 then captured else if i = 13 then temporary
    else if i = 16 ∨ i = 17 ∨ i = 21 ∨ i = 22 ∨ i = 23 then []
    else frame.stacks i

def initialState (frame : Data) (zero one : Word) (bs : List Block) : Data :=
  state frame frame.regs (encodeBlocks bs) zero one [] []

def finalState (frame : Data) (zero one code : Word) : Data :=
  state frame (fun _ => false) [] zero one code []

def reset : Code :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))

def construct : Code :=
  .call (ProgramLinking.liftProgram SubexpKernelControl.fixedProgram id kernelPorts)

def moveSource : Code :=
  .seq (.call (StackRoutines.transferProgram (20 : Fin 24) 13 (0 : Fin 3) 1))
    (.call (StackRoutines.transferProgram (13 : Fin 24) 1 (0 : Fin 3) 1))

def command : Code := .seq reset (.seq construct moveSource)

abbrev program : Program 3 24 176 := StructuredCalls.compiled command 20 1

theorem command_size : StructuredCalls.size command = 175 := rfl

theorem reset_eval (frame : Data) (regs : Fin 3 → Bool)
    (source zero one captured temporary : Word) :
    Eval reset 3 (state frame regs source zero one captured temporary)
      (state frame (fun _ => false) source zero one captured temporary) := by
  have h0 := StructuredProgram.Eval.atom (StructuredProgram.Atom.set (s := 24) 0 false)
    (state frame regs source zero one captured temporary)
  have h1 := StructuredProgram.Eval.atom (StructuredProgram.Atom.set (s := 24) 1 false)
    ((StructuredProgram.Atom.set (s := 24) 0 false).eval
      (state frame regs source zero one captured temporary))
  have h2 := StructuredProgram.Eval.atom (StructuredProgram.Atom.set (s := 24) 2 false)
    ((StructuredProgram.Atom.set (s := 24) 1 false).eval
      ((StructuredProgram.Atom.set (s := 24) 0 false).eval
        (state frame regs source zero one captured temporary)))
  have heq : (StructuredProgram.Atom.set (s := 24) 2 false).eval
      ((StructuredProgram.Atom.set (s := 24) 1 false).eval
        ((StructuredProgram.Atom.set (s := 24) 0 false).eval
          (state frame regs source zero one captured temporary))) =
      state frame (fun _ => false) source zero one captured temporary := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [state, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    · rfl
  rw [heq] at h2
  exact Eval.seq (.base h0) (Eval.seq (.base h1) (.base h2))

theorem embed_kernel (frame : Data) (source zero one captured temporary source' : Word) :
    embedState id kernelPorts
      (state frame (fun _ => false) source zero one captured temporary)
      (SubexpKernelControl.serviceState source' zero one) =
    state frame (fun _ => false) source' zero one captured temporary := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id kernelPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [state, kernelPorts, SubexpKernelControl.serviceState,
      SubexpKernelControl.state, SubexpKernelControl.emptyAccumulator]
  · intro i hi
    have h20 : i ≠ 20 := fun h => hi ⟨0, by simpa [kernelPorts] using h.symm⟩
    have h18 : i ≠ 18 := fun h => hi ⟨1, by simpa [kernelPorts] using h.symm⟩
    have h19 : i ≠ 19 := fun h => hi ⟨2, by simpa [kernelPorts] using h.symm⟩
    simp [state, h20, h18, h19]

theorem construct_eval (frame : Data) (zero one captured temporary : Word) (bs : List Block) :
    Eval construct
      (SubexpKernelControl.kernelCost zero one bs + 3 * (momentCode zero one bs).length + 6)
      (state frame (fun _ => false) (encodeBlocks bs) zero one captured temporary)
      (state frame (fun _ => false) (momentCode zero one bs) zero one captured temporary) := by
  have h := eval_call_lifted SubexpKernelControl.fixedProgram id kernelPorts
    (state frame (fun _ => false) (encodeBlocks bs) zero one captured temporary)
    Function.injective_id kernelPorts_injective (SubexpKernelControl.program_trace zero one bs)
  simpa only [embed_kernel, construct] using h

theorem transfer_eval (src dst : Fin 24) (h : src ≠ dst) (d : Data) :
    Eval (.call (StackRoutines.transferProgram src dst (0 : Fin 3) 1))
      (3 * (d.stacks src).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩ := by
  apply Eval.call
  exact ListRegisterProgram.transfer_run src dst 0 1 h (by decide) d.regs d.stacks

theorem moveSource_eval (frame : Data) (zero one code : Word) :
    Eval moveSource (6 * code.length + 6)
      (state frame (fun _ => false) code zero one [] [])
      (finalState frame zero one code) := by
  have h1 := transfer_eval 20 13 (by decide)
    (state frame (fun _ => false) code zero one [] [])
  have heq1 : (⟨readRegs (fun _ : Fin 3 => false) 0 1 none,
      StackRoutines.transferStacks (20 : Fin 24) 13
        (state frame (fun _ => false) code zero one [] []).stacks⟩ : Data) =
      state frame (fun _ => false) [] zero one [] code.reverse := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [readRegs]
    · funext i
      simp only [StackRoutines.transferStacks, Function.update_apply, state]
      by_cases h20 : i = 20 <;> by_cases h13 : i = 13 <;>
        simp_all
  change Eval _ (3 * code.length + 3) _
    (⟨readRegs (fun _ : Fin 3 => false) 0 1 none,
      StackRoutines.transferStacks (20 : Fin 24) 13
        (state frame (fun _ => false) code zero one [] []).stacks⟩ : Data) at h1
  rw [heq1] at h1
  have h2 := transfer_eval 13 1 (by decide)
    (state frame (fun _ => false) [] zero one [] code.reverse)
  have heq2 : (⟨readRegs (fun _ : Fin 3 => false) 0 1 none,
      StackRoutines.transferStacks (13 : Fin 24) 1
        (state frame (fun _ => false) [] zero one [] code.reverse).stacks⟩ : Data) =
      finalState frame zero one code := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i
      simp only [StackRoutines.transferStacks, Function.update_apply, state]
      by_cases h13 : i = 13 <;> by_cases h1 : i = 1 <;>
        simp_all
  change Eval _ (3 * code.reverse.length + 3) _
    (⟨readRegs (fun _ : Fin 3 => false) 0 1 none,
      StackRoutines.transferStacks (13 : Fin 24) 1
        (state frame (fun _ => false) [] zero one [] code.reverse).stacks⟩ : Data) at h2
  rw [heq2] at h2
  have h12 := Eval.seq h1 h2
  rw [List.length_reverse] at h12
  have hcost :
      (3 * code.length + 3) + (3 * code.length + 3) = 6 * code.length + 6 := by
    omega
  rw [hcost] at h12
  simpa only [moveSource] using h12

theorem command_eval (frame : Data) (zero one : Word) (bs : List Block) :
    Eval command
      (SubexpKernelControl.kernelCost zero one bs + 9 * (momentCode zero one bs).length + 15)
      (initialState frame zero one bs)
      (finalState frame zero one (momentCode zero one bs)) := by
  have h := Eval.seq (reset_eval frame frame.regs (encodeBlocks bs) zero one [] [])
    (Eval.seq (construct_eval frame zero one [] [] bs)
      (moveSource_eval frame zero one (momentCode zero one bs)))
  have hcost :
      3 + ((SubexpKernelControl.kernelCost zero one bs +
          3 * (momentCode zero one bs).length + 6) +
        (6 * (momentCode zero one bs).length + 6)) =
        SubexpKernelControl.kernelCost zero one bs +
          9 * (momentCode zero one bs).length + 15 := by
    omega
  rw [hcost] at h
  simpa only [command, initialState] using h

theorem program_trace (frame : Data) (zero one : Word) (bs : List Block) :
    Trace program
      (SubexpKernelControl.kernelCost zero one bs + 9 * (momentCode zero one bs).length + 16)
      ((initialState frame zero one bs).withPC (some program.entry))
      ((finalState frame zero one (momentCode zero one bs)).withPC none) := by
  have h := StructuredCalls.compiled_halt_trace (command_eval frame zero one bs) 20 1
  have hcost :
      (SubexpKernelControl.kernelCost zero one bs +
          9 * (momentCode zero one bs).length + 15) + 1 =
        SubexpKernelControl.kernelCost zero one bs +
          9 * (momentCode zero one bs).length + 16 := by
    omega
  rw [hcost] at h
  exact h

theorem program_expression_trace {R : Type*} [Zero R] [One R]
    (frame : Data) (encode : R → Word) (bs : List (SubexpAlgorithm.Block R)) :
    Trace program
      (SubexpKernelControl.kernelCost (encode 0) (encode 1)
          (bs.map (SubexpKernelControl.ofBlock encode)) +
        9 * (SubexpPostfixControl.serializeCode encode
          (SubexpAlgorithm.momentExpression bs).compile).length + 16)
      ((initialState frame (encode 0) (encode 1)
        (bs.map (SubexpKernelControl.ofBlock encode))).withPC (some program.entry))
      ((finalState frame (encode 0) (encode 1)
        (SubexpPostfixControl.serializeCode encode
          (SubexpAlgorithm.momentExpression bs).compile)).withPC none) := by
  simpa only [SubexpKernelControl.momentCode_eq] using
    program_trace frame (encode 0) (encode 1) (bs.map (SubexpKernelControl.ofBlock encode))

@[simp] theorem finalState_source (frame : Data) (zero one code : Word) :
    (finalState frame zero one code).stacks 1 = code := by simp [finalState, state]

theorem finalState_frame (frame : Data) (zero one code : Word) (i : Fin 24)
    (hi : i ≠ 1 ∧ i ≠ 13 ∧ i ≠ 16 ∧ i ≠ 17 ∧ i ≠ 18 ∧ i ≠ 19 ∧
      i ≠ 20 ∧ i ≠ 21 ∧ i ≠ 22 ∧ i ≠ 23) :
    (finalState frame zero one code).stacks i = frame.stacks i := by
  rcases hi with ⟨h1,h13,h16,h17,h18,h19,h20,h21,h22,h23⟩
  simp [finalState, state, *]

theorem master_ports_preserved (frame : Data) (zero one code : Word) :
    ∀ i ∈ ([0,2,3,14] : List (Fin 24)),
      (finalState frame zero one code).stacks i = frame.stacks i := by
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [finalState, state]

end SubexponentialSAT.SubexpKernelService

end OAI.Algorithms
