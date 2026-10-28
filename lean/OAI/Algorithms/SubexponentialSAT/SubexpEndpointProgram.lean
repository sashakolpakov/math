import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

/-!
# Binary prime-search endpoints by a fixed finite program

The binary input is the exponent itself, including any leading zeroes.  A
counted loop appends one bit per iteration to the endpoint words.  The final
increment is another finite bit program; the powers below occur only in the
correctness specification.
-/

namespace SubexponentialSAT.SubexpEndpointProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms
open SubexponentialSAT.SubexpParameterProgram (atoms runAtoms atoms_eval)

abbrev Data := StructuredProgram.State 3 6
abbrev Regs := Fin 3 → Bool

/-- Ports: exponent, controller scratch, lower, start, fuel, upper. -/
def state (r : Regs) (exponent scratch lower start fuel upper : List Bool) : Data :=
  ⟨r, ![exponent, scratch, lower, start, fuel, upper]⟩

def inputState (r : Regs) (exponent : List Bool) : Data :=
  state r exponent [] [] [] [] []

def powerWord (i : ℕ) : List Bool := List.replicate i false ++ [true]

def fuelWord (i : ℕ) : List Bool := List.replicate i true

@[simp] theorem powerWord_zero : powerWord 0 = [true] := rfl
@[simp] theorem powerWord_succ (i : ℕ) : powerWord (i + 1) = false :: powerWord i := by
  simp [powerWord, List.replicate_succ]
@[simp] theorem fuelWord_zero : fuelWord 0 = [] := rfl
@[simp] theorem fuelWord_succ (i : ℕ) : fuelWord (i + 1) = true :: fuelWord i := by
  simp [fuelWord, List.replicate_succ]
@[simp] theorem powerWord_length (i : ℕ) : (powerWord i).length = i + 1 := by
  simp [powerWord]
@[simp] theorem fuelWord_length (i : ℕ) : (fuelWord i).length = i := by
  simp [fuelWord]

@[simp] theorem powerWord_value (i : ℕ) : value (powerWord i) = 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih => simp [ih, pow_succ, Nat.mul_comm]

theorem fuelWord_value_add_one (i : ℕ) : value (fuelWord i) + 1 = 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih => simp only [fuelWord_succ, value_true_cons, pow_succ]; omega

@[simp] theorem fuelWord_value (i : ℕ) : value (fuelWord i) = 2 ^ i - 1 := by
  have h := fuelWord_value_add_one i
  omega

def ports : CounterForPrograms.Ports 3 6 :=
  ⟨Function.Embedding.refl _, 0, 1, by decide⟩

def initializeOps : List (StructuredProgram.Atom 3 6) :=
  [.set 0 true, .push 2 0, .push 3 0, .push 5 0, .set 0 false, .push 5 0]

abbrev seed : StructuredCalls.Cmd 3 6 := .base (atoms initializeOps)

def initialized (r : Regs) (exponent : List Bool) : Data :=
  state (Function.update r 0 false) exponent [] (powerWord 0) (powerWord 0)
    (fuelWord 0) (powerWord 1)

theorem seed_eval (r : Regs) (exponent : List Bool) :
    StructuredCalls.Eval seed 6 (inputState r exponent) (initialized r exponent) := by
  have h := atoms_eval initializeOps (inputState r exponent)
  have heq : runAtoms initializeOps (inputState r exponent) = initialized r exponent := by
    apply CounterForPrograms.data_ext
    · funext i; fin_cases i <;>
        simp [runAtoms, initializeOps, inputState, initialized, state,
          Atom.eval, Atom.instr, State.ofCfg, execInstr]
    · funext i; fin_cases i <;>
        simp [runAtoms, initializeOps, inputState, initialized, state,
          Atom.eval, Atom.instr, State.ofCfg, execInstr]
  rw [heq] at h
  exact .base (by simpa only [initializeOps, List.length_cons, List.length_nil] using h)

def bodyOps : List (StructuredProgram.Atom 3 6) :=
  [.set 0 false, .push 2 0, .push 3 0, .push 5 0, .set 0 true, .push 4 0]

abbrev body : StructuredCalls.Cmd 3 6 := .base (atoms bodyOps)

def bodyResult (d : Data) : Data := runAtoms bodyOps d

theorem body_eval (d : Data) : StructuredCalls.Eval body 6 d (bodyResult d) := by
  exact .base (by simpa only [bodyOps, bodyResult, List.length_cons, List.length_nil] using
    (atoms_eval bodyOps d))

@[simp] theorem bodyResult_stack_0 (d : Data) : (bodyResult d).stacks 0 = d.stacks 0 := by
  simp [bodyResult, runAtoms, bodyOps, Atom.eval, Atom.instr, State.ofCfg,
    execInstr]
@[simp] theorem bodyResult_stack_1 (d : Data) : (bodyResult d).stacks 1 = d.stacks 1 := by
  simp [bodyResult, runAtoms, bodyOps, Atom.eval, Atom.instr, State.ofCfg,
    execInstr]
@[simp] theorem bodyResult_stack_2 (d : Data) :
    (bodyResult d).stacks 2 = false :: d.stacks 2 := by
  simp [bodyResult, runAtoms, bodyOps, Atom.eval, Atom.instr, State.ofCfg,
    execInstr]
@[simp] theorem bodyResult_stack_3 (d : Data) :
    (bodyResult d).stacks 3 = false :: d.stacks 3 := by
  simp [bodyResult, runAtoms, bodyOps, Atom.eval, Atom.instr, State.ofCfg,
    execInstr]
@[simp] theorem bodyResult_stack_4 (d : Data) :
    (bodyResult d).stacks 4 = true :: d.stacks 4 := by
  simp [bodyResult, runAtoms, bodyOps, Atom.eval, Atom.instr, State.ofCfg,
    execInstr]
@[simp] theorem bodyResult_stack_5 (d : Data) :
    (bodyResult d).stacks 5 = false :: d.stacks 5 := by
  simp [bodyResult, runAtoms, bodyOps, Atom.eval, Atom.instr, State.ofCfg,
    execInstr]

def Invariant (i : ℕ) (d : Data) : Prop :=
  d.stacks 2 = powerWord i ∧ d.stacks 3 = powerWord i ∧
  d.stacks 4 = fuelWord i ∧ d.stacks 5 = powerWord (i + 1)

theorem invariant_initial (r : Regs) (exponent : List Bool) :
    Invariant 0 (initialized r exponent) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem invariant_stable : CounterForPrograms.FrameStable ports Invariant := by
  intro i a b h hi
  rcases hi with ⟨h₂, h₃, h₄, h₅⟩
  exact ⟨(h 2 (by decide) (by decide)).symm.trans h₂,
    (h 3 (by decide) (by decide)).symm.trans h₃,
    (h 4 (by decide) (by decide)).symm.trans h₄,
    (h 5 (by decide) (by decide)).symm.trans h₅⟩

theorem body_spec : CounterForPrograms.BodySpec ports body Invariant (fun _ => 6) := by
  intro i d hi hs _
  refine ⟨6, bodyResult d, le_rfl, body_eval d, bodyResult_stack_0 d, ?_, ?_⟩
  · simpa only [ports, bodyResult_stack_1] using hs
  · rcases hi with ⟨h₂, h₃, h₄, h₅⟩
    simp [Invariant, h₂, h₃, h₄, h₅]

abbrev buildPowers : StructuredCalls.Cmd 3 6 :=
  .seq seed (CounterForPrograms.forCmd ports body)

def loopBound (exponent : List Bool) : ℕ :=
  value exponent * 6 + (value exponent + 1) * (16 * exponent.length + 16)

theorem buildPowers_eval (r : Regs) (exponent : List Bool) :
    ∃ n d, StructuredCalls.Eval buildPowers n (inputState r exponent) d ∧
      Invariant (value exponent) d ∧ value (d.stacks 0) = 0 ∧
      (d.stacks 0).length = exponent.length ∧ d.stacks 1 = [] ∧
      n ≤ loopBound exponent + 6 := by
  obtain ⟨n, d, he, hi, hz, hw, hs, hn⟩ :=
    CounterForPrograms.for_correct ports body Invariant (fun _ => 6)
      invariant_stable body_spec (initialized r exponent) rfl
      (invariant_initial r exponent)
  refine ⟨6 + n, d, .seq (seed_eval r exponent) he,
    hi, hz, hw, hs, ?_⟩
  have hn' : n ≤ loopBound exponent := by
    simpa [loopBound, ports, initialized, state, CounterForPrograms.budgetSum_const] using hn
  omega

def incrementPorts : CounterForPrograms.Ports 3 6 :=
  ⟨Function.Embedding.refl _, 3, 1, by decide⟩

abbrev incrementStart : StructuredCalls.Cmd 3 6 :=
  .call (ProgramLinking.liftProgram (rippleProgram true) incrementPorts.register
    (CounterForPrograms.stackPorts incrementPorts))

noncomputable def incrementResult (d : Data) : Data :=
  CounterForPrograms.install incrementPorts d false false (d.regs 2)
    (ripple true (d.stacks 3)) []

theorem incrementStart_eval (d : Data) (hs : d.stacks 1 = []) :
    StructuredCalls.Eval incrementStart (rippleCost true (d.stacks 3) + 1)
      d (incrementResult d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram true) incrementPorts.register
    (CounterForPrograms.stackPorts incrementPorts) d incrementPorts.register.injective
    (CounterForPrograms.stackPorts incrementPorts).injective
    (CounterForPrograms.ripple_local_trace true (d.regs 0) (d.regs 1) (d.regs 2)
      (d.stacks 3))
  change StructuredCalls.Eval incrementStart _
    (CounterForPrograms.install incrementPorts d _ _ _ _ []) (incrementResult d) at h
  rw [← hs] at h
  have hi : CounterForPrograms.install incrementPorts d (d.regs 0) (d.regs 1)
      (d.regs 2) (d.stacks 3) (d.stacks 1) = d := by
    simpa [incrementPorts] using CounterForPrograms.install_self incrementPorts d
  rw [hi] at h
  exact h

@[simp] theorem incrementResult_start (d : Data) :
    (incrementResult d).stacks 3 = ripple true (d.stacks 3) :=
  CounterForPrograms.install_counter incrementPorts d _ _ _ _ _

@[simp] theorem incrementResult_scratch (d : Data) :
    (incrementResult d).stacks 1 = [] :=
  CounterForPrograms.install_scratch incrementPorts d _ _ _ _ _

theorem incrementResult_other (d : Data) (i : Fin 6) (hi₃ : i ≠ 3) (hi₁ : i ≠ 1) :
    (incrementResult d).stacks i = d.stacks i :=
  CounterForPrograms.install_other_stack incrementPorts d _ _ _ _ _ i hi₃ hi₁

/-- A fixed instruction table; the exponent remains input data. -/
abbrev command : StructuredCalls.Cmd 3 6 := .seq buildPowers incrementStart

def program := StructuredCalls.compiled command (0 : Fin 6) 3

theorem command_size : StructuredCalls.size command = 57 := by
  simp [ initializeOps, bodyOps,
    atoms, StructuredCalls.size, StructuredProgram.size]

def runtimeBound (exponent : List Bool) : ℕ :=
  loopBound exponent + 8 * (value exponent + 1) + 15

theorem runtimeBound_eq (exponent : List Bool) :
    runtimeBound exponent =
      16 * (value exponent + 1) * exponent.length + 30 * value exponent + 39 := by
  simp only [runtimeBound, loopBound]
  ring

/-- Exact generated words, including zero exponent and padded input. -/
def Output (exponent : List Bool) (d : Data) : Prop :=
  value (d.stacks 0) = 0 ∧ (d.stacks 0).length = exponent.length ∧ d.stacks 1 = [] ∧
  d.stacks 2 = powerWord (value exponent) ∧
  d.stacks 3 = ripple true (powerWord (value exponent)) ∧
  d.stacks 4 = fuelWord (value exponent) ∧
  d.stacks 5 = powerWord (value exponent + 1)

theorem command_eval (r : Regs) (exponent : List Bool) :
    ∃ n d, StructuredCalls.Eval command n (inputState r exponent) d ∧
      Output exponent d ∧ n + 1 ≤ runtimeBound exponent := by
  obtain ⟨n, d, he, hi, hz, hw, hs, hn⟩ := buildPowers_eval r exponent
  refine ⟨n + (rippleCost true (d.stacks 3) + 1), incrementResult d,
    .seq he (incrementStart_eval d hs), ?_, ?_⟩
  · rcases hi with ⟨h₂, h₃, h₄, h₅⟩
    exact ⟨by simpa only [incrementResult_other d 0 (by decide) (by decide)] using hz,
      by simpa only [incrementResult_other d 0 (by decide) (by decide)] using hw,
      incrementResult_scratch d,
      (incrementResult_other d 2 (by decide) (by decide)).trans h₂,
      by simp only [incrementResult_start, h₃],
      (incrementResult_other d 4 (by decide) (by decide)).trans h₄,
      (incrementResult_other d 5 (by decide) (by decide)).trans h₅⟩
  · have hb := rippleCost_le true (d.stacks 3)
    have hl : (d.stacks 3).length = value exponent + 1 := by
      rw [hi.2.1, powerWord_length]
    rw [hl] at hb
    dsimp [runtimeBound]
    omega

theorem run_output (r : Regs) (exponent : List Bool) :
    ∃ d, Output exponent d ∧
      BitProgram.RunsIn program (runtimeBound exponent)
        ((inputState r exponent).withPC (some program.entry)) (d.withPC none) := by
  obtain ⟨n, d, he, hout, hn⟩ := command_eval r exponent
  exact ⟨d, hout, n + 1, hn, StructuredCalls.compiled_halt_trace he 0 3⟩

theorem output_values (exponent : List Bool) (d : Data) (h : Output exponent d) :
    value (d.stacks 2) = 2 ^ value exponent ∧
    value (d.stacks 3) = 2 ^ value exponent + 1 ∧
    value (d.stacks 4) = 2 ^ value exponent - 1 ∧
    value (d.stacks 5) = 2 ^ (value exponent + 1) := by
  rcases h with ⟨_, _, _, h₂, h₃, h₄, h₅⟩
  simp [h₂, h₃, h₄, h₅, value_increment, pow_succ, Nat.mul_comm]

theorem output_values_toNat (exponent : List Bool) (d : Data) (h : Output exponent d) :
    BinaryArithmetic.toNat (d.stacks 2) = 2 ^ BinaryArithmetic.toNat exponent ∧
    BinaryArithmetic.toNat (d.stacks 3) = 2 ^ BinaryArithmetic.toNat exponent + 1 ∧
    BinaryArithmetic.toNat (d.stacks 4) = 2 ^ BinaryArithmetic.toNat exponent - 1 ∧
    BinaryArithmetic.toNat (d.stacks 5) = 2 ^ (BinaryArithmetic.toNat exponent + 1) := by
  simpa only [CounterPrograms.value_eq_toNat] using output_values exponent d h

theorem output_lengths (exponent : List Bool) (d : Data) (h : Output exponent d) :
    (d.stacks 2).length = value exponent + 1 ∧
    (d.stacks 3).length ≤ value exponent + 2 ∧
    (d.stacks 4).length = value exponent ∧
    (d.stacks 5).length = value exponent + 2 := by
  rcases h with ⟨_, _, _, h₂, h₃, h₄, h₅⟩
  refine ⟨by simp [h₂], ?_, by simp [h₄], by simp [h₅, Nat.add_assoc]⟩
  simpa only [h₃, powerWord_length, Nat.add_assoc] using
    ripple_length_le true (powerWord (value exponent))

theorem primitive_output (r : Regs) (exponent : List Bool) :
    ∃ d, Output exponent d ∧
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * runtimeBound exponent)
        (BitProgram.primitiveCfg program
          ((inputState r exponent).withPC (some program.entry)))
        (BitProgram.primitiveCfg program (d.withPC none)) := by
  obtain ⟨d, hout, hr⟩ := run_output r exponent
  exact ⟨d, hout, BitProgram.primitive_execution program hr⟩

/-- Call the same fixed program at arbitrary injective ports in a larger store.
Unassigned stacks and registers are preserved by `embedState`'s frame laws. -/
theorem lifted_output {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 6 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : StructuredProgram.State R S) (r : Regs) (exponent : List Bool) :
    ∃ n d, n ≤ runtimeBound exponent ∧ Output exponent d ∧
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram program register stack)) n
        (StructuredCalls.embedState register stack frame (inputState r exponent))
        (StructuredCalls.embedState register stack frame d) := by
  obtain ⟨n, d, he, hout, hn⟩ := command_eval r exponent
  exact ⟨n + 1, d, hn, hout,
    StructuredCalls.eval_call_lifted program register stack frame hregister hstack
      (StructuredCalls.compiled_halt_trace he 0 3)⟩

/-- Specialize to the exponent word produced by the actual parameter prefix. -/
theorem schedule_endpoints (r : Regs) (n : ℕ) (exponent : List Bool)
    (hu : BinaryArithmetic.toNat exponent = SubexpPackingParameters.u n) :
    ∃ d : Data,
      BinaryArithmetic.toNat (d.stacks 3) = 2 ^ SubexpPackingParameters.u n + 1 ∧
      BinaryArithmetic.toNat (d.stacks 4) = 2 ^ SubexpPackingParameters.u n - 1 ∧
      BitProgram.RunsIn program (runtimeBound exponent)
        ((inputState r exponent).withPC (some program.entry)) (d.withPC none) := by
  obtain ⟨d, hout, hr⟩ := run_output r exponent
  obtain ⟨_, hstart, hfuel, _⟩ := output_values_toNat exponent d hout
  exact ⟨d, by simpa only [hu] using hstart, by simpa only [hu] using hfuel, hr⟩

end SubexponentialSAT.SubexpEndpointProgram

end OAI.Algorithms
