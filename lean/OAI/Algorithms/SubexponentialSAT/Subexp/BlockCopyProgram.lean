import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# A fixed bit program for copying a local table into every block

Stack 0 contains the encoded local table, stack 1 the output suffix, stack 2
is empty scratch, and stack 3 contains the unary number of blocks.  The same
finite program handles all table lengths and block counts.  It preserves the
local table and prefixes one copy per block to the output.  This is the compact
block-major representation of the repeated local basis/complement arrays;
scattering their coordinates through the packing is a separate operation.
-/

namespace SubexponentialSAT.Subexp.BlockCopyProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := StructuredProgram.State 3 4

/-- An encoded table repeated in block order. -/
def copies (n : ℕ) (table : List Bool) : List Bool :=
  (List.replicate n table).flatten

@[simp] theorem copies_zero (table : List Bool) : copies 0 table = [] := rfl

theorem copies_succ (n : ℕ) (table : List Bool) :
    copies (n + 1) table = copies n table ++ table := by
  simp only [copies, List.replicate_succ', List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil]

@[simp] theorem copies_length (n : ℕ) (table : List Bool) :
    (copies n table).length = n * table.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [copies_succ, List.length_append, ih]; ring

def data (value active : Bool) (table output counter : List Bool) : Data :=
  ⟨![value, false, active], ![table, output, [], counter]⟩

/-- The loop state includes a pending copy when the active flag is true. -/
def loopState (n : ℕ) (table output : List Bool) : Data :=
  match n with
  | 0 => data false false table output []
  | n + 1 => data true true table output (List.replicate n true)

def initialState (n : ℕ) (table output : List Bool) : Data :=
  data false false table output (List.replicate n true)

abbrev popCount : Cmd 3 4 := .base (.atom (.pop 3 0 2))

abbrev copyTable : Cmd 3 4 := .call (copyProgram 0 1 2 (0 : Fin 3) 1)

abbrev body : Cmd 3 4 := .seq copyTable popCount

abbrev loop : Cmd 3 4 := .while 2 body

abbrev command : Cmd 3 4 := .seq popCount loop

/-- Twelve control labels, independent of the runtime block count/table size. -/
abbrev program : Program 3 4 (size command + 1) := compiled command 0 1

@[simp] theorem program_labels : size command + 1 = 12 := rfl

private theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

theorem popCount_eval (n : ℕ) (value active : Bool) (table output : List Bool) :
    Eval popCount 1 (data value active table output (List.replicate n true))
      (loopState n table output) := by
  have h : (StructuredProgram.Atom.pop (3 : Fin 4) (0 : Fin 3) 2).eval
      (data value active table output (List.replicate n true)) =
      loopState n table output := by
    apply state_ext
    · funext j
      cases n <;> fin_cases j <;>
        simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,
          execInstr, readRegs, data, loopState, List.replicate_succ]
    · funext j
      cases n <;> fin_cases j <;>
        simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,
          execInstr, data, loopState, List.replicate_succ]
  rw [← h]
  exact .base (.atom _ _)

theorem copyTable_eval (value active : Bool) (table output counter : List Bool) :
    Eval copyTable (7 * table.length + 5)
      (data value active table output counter)
      (data false active table (table ++ output) counter) := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace (0 : Fin 4) 1 2 (0 : Fin 3) 1
      (by decide) (by decide) (by decide) (by decide)
      (data value active table output counter).regs
      (data value active table output counter).stacks (by rfl)) 7 rfl rfl
  have hr : readRegs (data value active table output counter).regs 0 1 none =
      (data false active table (table ++ output) counter).regs := by
    funext j
    fin_cases j <;> simp [data, readRegs]
  have hs : copyStacks (0 : Fin 4) 1 (data value active table output counter).stacks =
      (data false active table (table ++ output) counter).stacks := by
    funext j
    fin_cases j <;> simp [data, copyStacks]
  simp only [copyResult] at h
  rw [hr, hs] at h
  simpa only [data, Matrix.cons_val_zero, StructuredProgram.State.withPC,
    copyProgram, Nat.add_assoc, Nat.reduceAdd] using h

theorem body_eval (n : ℕ) (table output : List Bool) :
    Eval body (7 * table.length + 6) (loopState (n + 1) table output)
      (loopState n table (table ++ output)) := by
  have h := Eval.seq (copyTable_eval true true table output (List.replicate n true))
    (popCount_eval n false true table (table ++ output))
  simpa only [body, loopState, Nat.add_assoc] using h

/-- Exact loop cost: every copied bit executes the already verified copy
routine, and every iteration includes the counter pop and loop guard. -/
theorem loop_eval (n : ℕ) (table output : List Bool) :
    Eval loop (n * (7 * table.length + 7) + 1)
      (loopState n table output)
      (loopState 0 table (copies n table ++ output)) := by
  induction n generalizing output with
  | zero =>
      simpa only [loop, Nat.zero_mul, Nat.zero_add, copies_zero, List.nil_append] using
        (Eval.while_false (test := (2 : Fin 3)) (body := body)
          (a := loopState 0 table output) rfl)
  | succ n ih =>
      have h := Eval.while_true (test := (2 : Fin 3)) (body := body)
        (a := loopState (n + 1) table output) (by rfl)
        (body_eval n table output) (ih (table ++ output))
      have hn : (7 * table.length + 6) + (n * (7 * table.length + 7) + 1) + 1 =
          (n + 1) * (7 * table.length + 7) + 1 := by ring
      simpa only [loop, hn, copies_succ, List.append_assoc] using h

theorem command_eval (n : ℕ) (table output : List Bool) :
    Eval command (n * (7 * table.length + 7) + 2)
      (initialState n table output)
      (data false false table (copies n table ++ output) []) := by
  have h := Eval.seq (popCount_eval n false false table output) (loop_eval n table output)
  have hn : 1 + (n * (7 * table.length + 7) + 1) =
      n * (7 * table.length + 7) + 2 := by omega
  simpa only [command, initialState, loopState, hn] using h

/-- The compiled finite Boolean-stack machine has the claimed exact trace. -/
theorem program_trace (n : ℕ) (table output : List Bool) :
    Trace program (n * (7 * table.length + 7) + 3)
      ((initialState n table output).withPC (some program.entry))
      ((data false false table (copies n table ++ output) []).withPC none) := by
  simpa only [program, Nat.add_assoc] using
    compiled_halt_trace (command_eval n table output) 0 1

/-- The verified compiler supplies a run of the fixed binary machine. Its
constant overhead is independent of both input lengths. -/
theorem program_primitive (n : ℕ) (table output : List Bool) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (n * (7 * table.length + 7) + 3))
      (primitiveCfg program ((initialState n table output).withPC (some program.entry)))
      (primitiveCfg program
        ((data false false table (copies n table ++ output) []).withPC none)) :=
  primitive_trace _ (program_trace n table output)

/-- In particular the global work is linear in the block count and encoded
local-table length; neither changes the program's finite control. -/
theorem trace_bound {n D L : ℕ} (table : List Bool)
    (hn : n ≤ D) (hL : table.length ≤ L) :
    n * (7 * table.length + 7) + 3 ≤ 7 * D * (L + 1) + 3 := by
  calc
    _ ≤ D * (7 * L + 7) + 3 := by gcongr
    _ = _ := by ring

end SubexponentialSAT.Subexp.BlockCopyProgram

end OAI.Algorithms
