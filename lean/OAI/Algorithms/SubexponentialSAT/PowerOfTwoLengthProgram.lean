import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredProgram
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms

/-!
# A power-of-two word from an input length

For a compile-time constant c, this fixed program consumes a word w and writes
c + 2 * length(w) zero bits followed by one true bit.  The runtime loop consumes
one Boolean cell per iteration; no natural-number register or semantic length
instruction occurs in the machine.
-/

namespace SubexponentialSAT.PowerOfTwoLengthProgram

open BitProgram StructuredProgram

abbrev Data := StructuredProgram.State 3 3

abbrev regs (bit present : Bool) : Fin 3 → Bool := ![false, bit, present]
abbrev stackData (input output : List Bool) : Fin 3 → List Bool := ![[], input, output]
abbrev state (bit present : Bool) (input output : List Bool) : Data :=
  ⟨regs bit present, stackData input output⟩

abbrev ready (input output : List Bool) : Data :=
  state (input.headD false) (!input.isEmpty) input.tail output

@[simp] theorem regs_zero (b p : Bool) : regs b p 0 = false := rfl
@[simp] theorem regs_one (b p : Bool) : regs b p 1 = b := rfl
@[simp] theorem regs_two (b p : Bool) : regs b p 2 = p := rfl
@[simp] theorem stacks_zero (input output : List Bool) : stackData input output 0 = [] := rfl
@[simp] theorem stacks_one (input output : List Bool) : stackData input output 1 = input := rfl
@[simp] theorem stacks_two (input output : List Bool) : stackData input output 2 = output := rfl

abbrev pushZero : StructuredProgram.Cmd 3 3 := .atom (.push 2 0)
abbrev popInput : StructuredProgram.Cmd 3 3 := .atom (.pop 1 1 2)
abbrev loopBody : StructuredProgram.Cmd 3 3 := .seq pushZero (.seq pushZero popInput)
abbrev loop : StructuredProgram.Cmd 3 3 := .while 2 loopBody
abbrev scan : StructuredProgram.Cmd 3 3 := .seq popInput loop

/-- Only this compile-time recursion changes the number of control labels. -/
abbrev fixedPush : ℕ → StructuredProgram.Cmd 3 3
  | 0 => .skip
  | n + 1 => .seq pushZero (fixedPush n)

abbrev initializeCmd : StructuredProgram.Cmd 3 3 :=
  .seq (.atom (.set 0 true)) (.seq (.atom (.push 2 0)) (.atom (.set 0 false)))

abbrev command (c : ℕ) : StructuredProgram.Cmd 3 3 :=
  .seq initializeCmd (.seq (fixedPush c) scan)

private theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

@[simp] theorem update_regs_one (b p x : Bool) :
    Function.update (regs b p) 1 x = regs x p := by
  funext j; fin_cases j <;> simp [regs]
@[simp] theorem update_regs_two (b p x : Bool) :
    Function.update (regs b p) 2 x = regs b x := by
  funext j; fin_cases j <;> simp [regs]
@[simp] theorem update_stacks_one (input output next : List Bool) :
    Function.update (stackData input output) 1 next = stackData next output := by
  funext j; fin_cases j <;> simp [stackData]
@[simp] theorem update_stacks_two (input output next : List Bool) :
    Function.update (stackData input output) 2 next = stackData input next := by
  funext j; fin_cases j <;> simp [stackData]

theorem push_eval (b p : Bool) (input output : List Bool) :
    StructuredProgram.Eval pushZero 1 (state b p input output)
      (state b p input (false :: output)) := by
  convert StructuredProgram.Eval.atom (.push (2 : Fin 3) 0) (state b p input output) using 1
  simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state]

theorem pop_eval (b p : Bool) (input output : List Bool) :
    StructuredProgram.Eval popInput 1 (state b p input output) (ready input output) := by
  convert StructuredProgram.Eval.atom (.pop (1 : Fin 3) 1 2) (state b p input output) using 1
  cases input <;>
    simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state, ready,
      readRegs]

theorem fixedPush_eval (c : ℕ) (b p : Bool) (input output : List Bool) :
    StructuredProgram.Eval (fixedPush c) c (state b p input output)
      (state b p input (List.replicate c false ++ output)) := by
  induction c generalizing output with
  | zero => simpa [fixedPush] using StructuredProgram.Eval.skip (state b p input output)
  | succ c ih =>
      have h := (push_eval b p input output).seq (ih (false :: output))
      have hl : List.replicate c false ++ false :: output =
          List.replicate (c + 1) false ++ output := by
        rw [List.replicate_add]
        simp [List.append_assoc]
      simpa only [fixedPush, Nat.add_comm 1 c, hl] using h

theorem loop_eval (input output : List Bool) :
    StructuredProgram.Eval loop (4 * input.length + 1) (ready input output)
      (state false false [] (List.replicate (2 * input.length) false ++ output)) := by
  induction input generalizing output with
  | nil =>
      simpa [loop, ready, state, regs] using
        (StructuredProgram.Eval.while_false (test := (2 : Fin 3)) (body := loopBody)
          (a := ready [] output) rfl)
  | cons bit rest ih =>
      have hb := (push_eval bit true rest output).seq
        ((push_eval bit true rest (false :: output)).seq
          (pop_eval bit true rest (false :: false :: output)))
      have h := StructuredProgram.Eval.while_true (test := (2 : Fin 3))
        (body := loopBody) (a := ready (bit :: rest) output) rfl hb
        (ih (false :: false :: output))
      have hl : List.replicate (2 * rest.length) false ++ false :: false :: output =
          List.replicate (2 * (bit :: rest).length) false ++ output := by
        rw [List.length_cons, Nat.mul_add, List.replicate_add]
        simp [List.append_assoc]
      rw [hl] at h
      convert h using 1
      simp only [List.length_cons]
      omega

theorem scan_eval (b p : Bool) (input output : List Bool) :
    StructuredProgram.Eval scan (4 * input.length + 2) (state b p input output)
      (state false false [] (List.replicate (2 * input.length) false ++ output)) := by
  have h := (pop_eval b p input output).seq (loop_eval input output)
  convert h using 1
  omega

theorem initializeCmd_eval (input : List Bool) :
    StructuredProgram.Eval initializeCmd 3 (state false false input [])
      (state false false input [true]) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) true)
    (state false false input [])).seq
    ((StructuredProgram.Eval.atom (.push (2 : Fin 3) 0) _).seq
      (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) _))
  convert h using 1
  simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state, regs,
    Function.update_idem]

def output (c : ℕ) (input : List Bool) : List Bool :=
  List.replicate (c + 2 * input.length) false ++ [true]

theorem output_value (c : ℕ) (input : List Bool) :
    BinaryArithmetic.toNat (output c input) = 2 ^ (c + 2 * input.length) := by
  have h : ∀ n : ℕ, BinaryArithmetic.toNat (List.replicate n false ++ [true]) = 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [List.replicate_succ, ih, pow_succ, Nat.mul_comm]
  exact h _

@[simp] theorem output_length (c : ℕ) (input : List Bool) :
    (output c input).length = c + 2 * input.length + 1 := by simp [output]

theorem command_eval (c : ℕ) (input : List Bool) :
    StructuredProgram.Eval (command c) (c + 4 * input.length + 5)
      (state false false input []) (state false false [] (output c input)) := by
  have h := (initializeCmd_eval input).seq
    ((fixedPush_eval c false false input [true]).seq
      (scan_eval false false input (List.replicate c false ++ [true])))
  have hl : List.replicate (2 * input.length) false ++ (List.replicate c false ++ [true]) =
      output c input := by
    rw [← List.append_assoc, ← List.replicate_add, Nat.add_comm]
    rfl
  rw [hl] at h
  convert h using 1
  · omega

@[simp] theorem size_command (c : ℕ) : StructuredProgram.size (command c) = c + 8 := by
  have hp : StructuredProgram.size (fixedPush c) = c := by
    induction c with
    | zero => rfl
    | succ c ih => simp [ StructuredProgram.size, ih, Nat.add_comm]
  simp [
    StructuredProgram.size, hp, Nat.add_comm, Nat.add_left_comm]

/-- There are c+9 control labels; c is a compile-time constant. -/
def program (c : ℕ) := StructuredProgram.compiled (command c) (1 : Fin 3) 2

private theorem state_input (input : List Bool) :
    state false false input [] = StructuredProgram.ioState (1 : Fin 3) input := by
  apply state_ext
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> simp [ stackData ]

private theorem state_output (result : List Bool) :
    state false false [] result = StructuredProgram.ioState (2 : Fin 3) result := by
  apply state_ext
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> simp [ stackData ]

/-- Complete clean input-to-output execution, with an exact linear cost. -/
theorem run_trace (c : ℕ) (input : List Bool) :
    BitProgram.Trace (program c) (c + 4 * input.length + 6)
      (BitProgram.initial (program c) input)
      (BitProgram.terminal (program c) (output c input)) := by
  have h := command_eval c input
  rw [state_input, state_output] at h
  convert StructuredProgram.compiled_io_trace 1 2 h using 1
  all_goals first | rfl

theorem run_correct (c : ℕ) (input : List Bool) :
    BitProgram.RunsIn (program c) (c + 4 * input.length + 6)
      (BitProgram.initial (program c) input)
      (BitProgram.terminal (program c)
        (List.replicate (c + 2 * input.length) false ++ [true])) :=
  ⟨_, le_rfl, run_trace c input⟩

theorem primitive_correct (c : ℕ) (input : List Bool) :
    Computation.RunsIn (BitProgram.primitive (program c)).step
      (BitProgram.primitiveOverhead (program c) * (c + 4 * input.length + 6))
      (BitProgram.primitiveCfg (program c) (BitProgram.initial (program c) input))
      (BitProgram.primitiveCfg (program c)
        (BitProgram.terminal (program c) (output c input))) :=
  BitProgram.primitive_execution _ (run_correct c input)

end SubexponentialSAT.PowerOfTwoLengthProgram

end OAI.Algorithms
