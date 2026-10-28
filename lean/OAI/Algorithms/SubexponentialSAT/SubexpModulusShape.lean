import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# A fixed program constructing the modulus output width

The input counter is a little-endian binary word. The program starts a shape
stack with one cell and prefixes one copy of the base word per countdown step.
Its shape therefore has length `1 + exponent * base.length`; no unbounded
natural-number operation is an instruction of the program.
-/

namespace SubexponentialSAT.SubexpModulusShape

open BitProgram StructuredProgram StructuredCalls BinaryArithmetic

abbrev Regs := Fin 8 → Bool
abbrev Data := StructuredProgram.State 8 5

/-- Base, binary counter, output shape, copy scratch, counter scratch. -/
def stackState (base counter shape : List Bool) : Fin 5 → List Bool :=
  ![base, counter, shape, [], []]

def state (r : Regs) (base counter shape : List Bool) : Data :=
  ⟨r, stackState base counter shape⟩

@[simp] theorem stack_base (base counter shape : List Bool) :
    stackState base counter shape 0 = base := rfl

@[simp] theorem stack_shape (base counter shape : List Bool) :
    stackState base counter shape 2 = shape := rfl

@[simp] theorem update_shape (base counter shape next : List Bool) :
    Function.update (stackState base counter shape) 2 next =
      stackState base counter next := by
  funext i
  fin_cases i <;> simp [stackState]

def ports : CounterForPrograms.Ports 8 5 where
  register := ⟨fun i => ⟨i.val, by omega⟩, by
    intro a b h
    apply Fin.ext
    exact congrArg (fun k : Fin 8 => k.val) h⟩
  counter := 1
  scratch := 4
  counter_ne_scratch := by decide

abbrev copyBase : StructuredCalls.Cmd 8 5 :=
  .call (StackRoutines.copyProgram 0 2 3 0 1)

theorem copy_eval (r : Regs) (base counter shape : List Bool) :
    StructuredCalls.Eval copyBase (7 * base.length + 5)
      (state r base counter shape)
      (state (readRegs r 0 1 none) base counter (base ++ shape)) := by
  apply StructuredCalls.Eval.call
  have h := StackRoutines.copyProgram_trace (0 : Fin 5) 2 3 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) r (stackState base counter shape) rfl
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [state, StackRoutines.copyResult, StackRoutines.copyStacks] using hh

def Invariant (base : List Bool) (i : ℕ) (d : Data) : Prop :=
  d.stacks 0 = base ∧ (d.stacks 2).length = 1 + i * base.length ∧ d.stacks 3 = []

theorem invariant_initial (r : Regs) (base counter : List Bool) :
    Invariant base 0 (state r base counter [false]) := by
  simp [Invariant, state, stackState]

theorem state_of_invariant (base : List Bool) (i : ℕ) (d : Data)
    (hi : Invariant base i d) (hs : d.stacks 4 = []) :
    d = state d.regs base (d.stacks 1) (d.stacks 2) := by
  rcases d with ⟨r, stk⟩
  apply congrArg (StructuredProgram.State.mk r)
  funext j
  fin_cases j
  · exact hi.1
  · rfl
  · rfl
  · exact hi.2.2
  · exact hs

theorem invariant_frameStable (base : List Bool) :
    CounterForPrograms.FrameStable ports (Invariant base) := by
  intro i a b hf hi
  refine ⟨?_, ?_, ?_⟩
  · exact (hf 0 (by decide) (by decide)).symm.trans hi.1
  · rw [← hf 2 (by decide) (by decide)]
    exact hi.2.1
  · exact (hf 3 (by decide) (by decide)).symm.trans hi.2.2

theorem copy_spec (base : List Bool) :
    CounterForPrograms.BodySpec ports copyBase (Invariant base)
      (fun _ => 7 * base.length + 5) := by
  intro i d hi hs _
  let e := state (readRegs d.regs 0 1 none) base (d.stacks 1) (base ++ d.stacks 2)
  refine ⟨7 * base.length + 5, e, le_rfl, ?_, rfl, rfl, ?_⟩
  · have ht := copy_eval d.regs base (d.stacks 1) (d.stacks 2)
    rwa [← state_of_invariant base i d hi hs] at ht
  · refine ⟨rfl, ?_, rfl⟩
    change (base ++ d.stacks 2).length = _
    rw [List.length_append, hi.2.1]
    ring

abbrev initShape : StructuredCalls.Cmd 8 5 :=
  .base (.seq (.atom (.set 0 false)) (.atom (.push 2 0)))

theorem initShape_eval (r : Regs) (base counter : List Bool) :
    StructuredCalls.Eval initShape 2 (state r base counter [])
      (state (Function.update r 0 false) base counter [false]) := by
  apply StructuredCalls.Eval.base
  have hs := StructuredProgram.Eval.atom (.set (0 : Fin 8) false) (state r base counter [])
  have hp := StructuredProgram.Eval.atom (.push (2 : Fin 5) 0)
    (Atom.eval (.set (0 : Fin 8) false) (state r base counter []))
  simpa [Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr, state] using
    StructuredProgram.Eval.seq hs hp

abbrev command : StructuredCalls.Cmd 8 5 :=
  .seq initShape (CounterForPrograms.forCmd ports copyBase)

/-- The instruction table is independent of the two input words. -/
def program := StructuredCalls.compiled command (0 : Fin 5) 2

theorem command_size : StructuredCalls.size command = 44 := by
  rfl

def runtimeBound (base counter : List Bool) : ℕ :=
  BinaryArithmetic.toNat counter * (7 * base.length + 5) +
    (BinaryArithmetic.toNat counter + 1) * (16 * counter.length + 16) + 3

theorem command_eval (r : Regs) (base counter : List Bool) :
    ∃ n rf remaining shape,
      StructuredCalls.Eval command n (state r base counter [])
        (state rf base remaining shape) ∧
      shape.length = 1 + BinaryArithmetic.toNat counter * base.length ∧
      BinaryArithmetic.toNat remaining = 0 ∧ remaining.length = counter.length ∧
      n + 1 ≤ runtimeBound base counter := by
  obtain ⟨n, d, he, hi, hz, hw, hs, hn⟩ :=
    CounterForPrograms.for_correct ports copyBase (Invariant base)
      (fun _ => 7 * base.length + 5) (invariant_frameStable base) (copy_spec base)
      (state (Function.update r 0 false) base counter [false]) rfl
      (invariant_initial _ base counter)
  have hi' : Invariant base (BinaryArithmetic.toNat counter) d := by
    simpa [state, stackState, ports, CounterPrograms.value_eq_toNat] using hi
  have hz' : BinaryArithmetic.toNat (d.stacks 1) = 0 := by
    simpa [ports, CounterPrograms.value_eq_toNat] using hz
  have hw' : (d.stacks 1).length = counter.length := by
    simpa [state, stackState, ports] using hw
  have hn' : n ≤ BinaryArithmetic.toNat counter * (7 * base.length + 5) +
      (BinaryArithmetic.toNat counter + 1) * (16 * counter.length + 16) := by
    simpa [state, stackState, ports, CounterPrograms.value_eq_toNat,
      CounterForPrograms.budgetSum_const] using hn
  have hd := state_of_invariant base (BinaryArithmetic.toNat counter) d hi' hs
  refine ⟨2 + n, d.regs, d.stacks 1, d.stacks 2, ?_, hi'.2.1, hz', hw', ?_⟩
  · rw [← hd]
    exact .seq (initShape_eval r base counter) he
  · dsimp [runtimeBound]
    omega

/-- The output width and the entire countdown are proved from an actual
halted trace of one fixed 45-label Boolean program. -/
theorem run_width (r : Regs) (base counter : List Bool) :
    ∃ rf remaining shape,
      shape.length = 1 + BinaryArithmetic.toNat counter * base.length ∧
      BinaryArithmetic.toNat remaining = 0 ∧ remaining.length = counter.length ∧
      BitProgram.RunsIn program (runtimeBound base counter)
        ((state r base counter []).withPC (some program.entry))
        ((state rf base remaining shape).withPC none) := by
  obtain ⟨n, rf, remaining, shape, he, hl, hz, hw, hn⟩ := command_eval r base counter
  exact ⟨rf, remaining, shape, hl, hz, hw, n + 1, hn,
    StructuredCalls.compiled_halt_trace he 0 2⟩

theorem primitive_width (r : Regs) (base counter : List Bool) :
    ∃ rf remaining shape,
      shape.length = 1 + BinaryArithmetic.toNat counter * base.length ∧
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * runtimeBound base counter)
        (BitProgram.primitiveCfg program ((state r base counter []).withPC (some program.entry)))
        (BitProgram.primitiveCfg program ((state rf base remaining shape).withPC none)) := by
  obtain ⟨rf, remaining, shape, hl, _, _, ht⟩ := run_width r base counter
  exact ⟨rf, remaining, shape, hl, BitProgram.primitive_execution program ht⟩

end SubexponentialSAT.SubexpModulusShape

end OAI.Algorithms
