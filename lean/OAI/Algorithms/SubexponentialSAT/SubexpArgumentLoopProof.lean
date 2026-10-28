import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentEmitLoop

namespace OAI.Algorithms

/-!
Execution of the fixed row/column controller.  Every counter below is represented
by a runtime unary stack; the definitions are specifications of machine states,
not parameters of the instruction table.
-/

namespace SubexponentialSAT.SubexpArgumentEmitLoop

open BitProgram StructuredCalls

abbrev unary (n : ℕ) : List Bool := List.replicate n true

def flags (v p mark u saved : Bool) : Fin 5 → Bool :=
  fun i => if i = 0 then v else if i = 1 then p else if i = 2 then mark
    else if i = 3 then u else saved

@[simp] theorem flags_zero (v p mark u saved : Bool) : flags v p mark u saved 0 = v := rfl
@[simp] theorem flags_one (v p mark u saved : Bool) : flags v p mark u saved 1 = p := rfl
@[simp] theorem flags_two (v p mark u saved : Bool) : flags v p mark u saved 2 = mark := rfl
@[simp] theorem flags_three (v p mark u saved : Bool) : flags v p mark u saved 3 = u := rfl

@[simp] theorem update_flags_zero (v p mark u saved b : Bool) :
    Function.update (flags v p mark u saved) 0 b = flags b p mark u saved := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_flags_one (v p mark u saved b : Bool) :
    Function.update (flags v p mark u saved) 1 b = flags v b mark u saved := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_flags_two (v p mark u saved b : Bool) :
    Function.update (flags v p mark u saved) 2 b = flags v p b u saved := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_flags_three (v p mark u saved b : Bool) :
    Function.update (flags v p mark u saved) 3 b = flags v p mark b saved := by
  funext i; fin_cases i <;> rfl

@[simp] theorem read_flags (v p mark u saved : Bool) (top : Option Bool) :
    readRegs (flags v p mark u saved) 0 1 top =
      flags (top.getD false) top.isSome mark u saved := by simp [readRegs]
@[simp] theorem finished_flags (v p mark u saved : Bool) :
    SubexpArgumentProgram.finishedRegs (flags v p mark u saved) =
      flags true false mark u saved := by simp [SubexpArgumentProgram.finishedRegs]

def masters (D B i right j remaining rows : ℕ) : Fin 8 → List Bool :=
  fun k => if k = 0 then unary D else if k = 1 then unary B else if k = 2 then unary i
    else if k = 3 then unary right else if k = 4 then unary j
    else if k = 5 then unary remaining else if k = 6 then unary rows else []

/-- The four key-counter slots are exposed during calls, and are empty between
terms.  The remaining counters belong to the row/column controller. -/
def machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) : State 5 15 :=
  world (flags v p mark u saved) input [] (unary left) output (unary keyRight)
    (unary z) (unary width) (masters D B i right j remaining rows)

@[simp] theorem machine_eta (v p mark u saved v' p' mark' u' saved' : Bool)
    (input output : List Bool) (left keyRight z width D B i right j remaining rows : ℕ) :
    ({ regs := flags v p mark u saved,
       «stacks» := (machine v' p' mark' u' saved' input output
         left keyRight z width D B i right j remaining rows).stacks } : State 5 15) =
      machine v p mark u saved input output
        left keyRight z width D B i right j remaining rows := by
  rfl

abbrev ready (v p mark u saved : Bool) (input output : List Bool)
    (D B i right j remaining rows : ℕ) : State 5 15 :=
  machine v p mark u saved input output 0 0 0 0 D B i right j remaining rows

/-- Framed term prepending, with the exact key used by the concrete key loop. -/
def prepend (left right j B : ℕ) (mark u : Bool) (coefficient output : List Bool) : List Bool :=
  true :: (Encoding.frame (SubexpArgumentProgram.recordBody
    (SubexpArgumentKeyEmitter.paddedKey left right j B mark u) coefficient) ++ output)

def preparedCost (left right j B : ℕ) (mark u : Bool) (coefficient : List Bool) : ℕ :=
  SubexpArgumentKeyEmitter.rawCost left right j mark u +
    4 * (B - (SubexpArgumentKeyEmitter.rawKey left right j mark u).length) + 3 +
    (29 * coefficient.length +
      21 * (SubexpArgumentKeyEmitter.paddedKey left right j B mark u).length + 46)

theorem prepared_machine (v p mark u saved : Bool) (coefficient tail output : List Bool)
    (left keyRight z D B i right j remaining rows : ℕ) :
    Eval emitPrepared (preparedCost left keyRight z B mark u coefficient)
      (machine v p mark u saved (Encoding.frame coefficient ++ tail) output
        left keyRight z B D B i right j remaining rows)
      (ready true false mark u saved tail
        (prepend left keyRight z B mark u coefficient output) D B i right j remaining rows) := by
  simpa only [machine, ready, unary, flags_two, flags_three, finished_flags, prepend,
    preparedCost, List.replicate_zero]
    using emitPrepared_eval left keyRight z B (flags v p mark u saved) coefficient tail output
      (masters D B i right j remaining rows)

/-- Generic single-atom execution, useful for the concrete counter updates. -/
theorem atom_set_eval (dst : Fin 5) (b : Bool) (d : State 5 15) :
    Eval (atom (.set dst b)) 1 d ⟨Function.update d.regs dst b, d.stacks⟩ := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem atom_pop_eval (src : Fin 15) (d : State 5 15) :
    Eval (atom (.pop src 0 1)) 1 d
      ⟨readRegs d.regs 0 1 (d.stacks src).head?,
        Function.update d.stacks src (d.stacks src).tail⟩ := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem pushTrue_eval (dst : Fin 15) (d : State 5 15) :
    Eval (pushTrue dst) 2 d
      ⟨Function.update d.regs 0 true, Function.update d.stacks dst (true :: d.stacks dst)⟩ := by
  exact Eval.seq (atom_set_eval 0 true d)
    (Eval.base (StructuredProgram.Eval.atom _ _))

@[simp] theorem machine_regs (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).regs = flags v p mark u saved := rfl

@[simp] theorem machine_stack_0 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 0 = input := rfl

@[simp] theorem machine_stack_1 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 1 = [] := rfl

@[simp] theorem machine_stack_2 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 2 = unary left := rfl

@[simp] theorem machine_stack_3 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 3 = output := rfl

@[simp] theorem machine_stack_4 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 4 = unary keyRight := rfl

@[simp] theorem machine_stack_5 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 5 = unary z := rfl

@[simp] theorem machine_stack_6 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 6 = unary width := rfl

@[simp] theorem machine_stack_7 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 7 = unary D := rfl

@[simp] theorem machine_stack_8 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 8 = unary B := rfl

@[simp] theorem machine_stack_9 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 9 = unary i := rfl

@[simp] theorem machine_stack_10 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 10 = unary right := rfl

@[simp] theorem machine_stack_11 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 11 = unary j := rfl

@[simp] theorem machine_stack_12 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 12 = unary remaining := rfl

@[simp] theorem machine_stack_13 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 13 = unary rows := rfl

@[simp] theorem machine_stack_14 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 14 = [] := rfl

@[simp] theorem machine_update_2 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (n : ℕ) :
    Function.update (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 2 (unary n) =
      (machine v p mark u saved input output n keyRight z width D B i right j remaining rows).stacks := by
  funext k; fin_cases k <;> rfl

@[simp] theorem machine_update_4 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (n : ℕ) :
    Function.update (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 4 (unary n) =
      (machine v p mark u saved input output left n z width D B i right j remaining rows).stacks := by
  funext k; fin_cases k <;> rfl

@[simp] theorem machine_update_5 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (n : ℕ) :
    Function.update (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 5 (unary n) =
      (machine v p mark u saved input output left keyRight n width D B i right j remaining rows).stacks := by
  funext k; fin_cases k <;> rfl

@[simp] theorem machine_update_6 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (n : ℕ) :
    Function.update (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 6 (unary n) =
      (machine v p mark u saved input output left keyRight z n D B i right j remaining rows).stacks := by
  funext k; fin_cases k <;> rfl

@[simp] theorem machine_update_9 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (n : ℕ) :
    Function.update (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 9 (unary n) =
      (machine v p mark u saved input output left keyRight z width D B n right j remaining rows).stacks := by
  funext k; fin_cases k <;> rfl

@[simp] theorem machine_update_10 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (n : ℕ) :
    Function.update (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 10 (unary n) =
      (machine v p mark u saved input output left keyRight z width D B i n j remaining rows).stacks := by
  funext k; fin_cases k <;> rfl

@[simp] theorem machine_update_11 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (n : ℕ) :
    Function.update (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 11 (unary n) =
      (machine v p mark u saved input output left keyRight z width D B i right n remaining rows).stacks := by
  funext k; fin_cases k <;> rfl

@[simp] theorem machine_update_12 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (n : ℕ) :
    Function.update (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 12 (unary n) =
      (machine v p mark u saved input output left keyRight z width D B i right j n rows).stacks := by
  funext k; fin_cases k <;> rfl

@[simp] theorem machine_update_13 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (n : ℕ) :
    Function.update (machine v p mark u saved input output left keyRight z width D B i right j remaining rows).stacks 13 (unary n) =
      (machine v p mark u saved input output left keyRight z width D B i right j remaining n).stacks := by
  funext k; fin_cases k <;> rfl

theorem copy_9_2 (v p mark u saved : Bool) (input output : List Bool)
    (_left keyRight z width D B i right j remaining rows : ℕ) :
    Eval (copyWord 9 2) (7 * i + 5)
      (machine v p mark u saved input output 0 keyRight z width D B i right j remaining rows)
      (machine false false mark u saved input output i keyRight z width D B i right j remaining rows) := by
  have h := copyWord_eval 9 2 (by decide) (by decide) (by decide)
    (machine v p mark u saved input output 0 keyRight z width D B i right j remaining rows) rfl
  simpa only [machine_stack_9, List.length_replicate, StackRoutines.copyStacks,
    machine_stack_2, List.replicate_zero, List.append_nil, machine_update_2,
    machine_regs, read_flags, Option.getD_none, Option.isSome_none, machine_eta] using h

theorem copy_10_4 (v p mark u saved : Bool) (input output : List Bool)
    (left _keyRight z width D B i right j remaining rows : ℕ) :
    Eval (copyWord 10 4) (7 * right + 5)
      (machine v p mark u saved input output left 0 z width D B i right j remaining rows)
      (machine false false mark u saved input output left right z width D B i right j remaining rows) := by
  have h := copyWord_eval 10 4 (by decide) (by decide) (by decide)
    (machine v p mark u saved input output left 0 z width D B i right j remaining rows) rfl
  simpa only [machine_stack_10, List.length_replicate, StackRoutines.copyStacks,
    machine_stack_4, List.replicate_zero, List.append_nil, machine_update_4,
    machine_regs, read_flags, Option.getD_none, Option.isSome_none, machine_eta] using h

theorem copy_11_5 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight _z width D B i right j remaining rows : ℕ) :
    Eval (copyWord 11 5) (7 * j + 5)
      (machine v p mark u saved input output left keyRight 0 width D B i right j remaining rows)
      (machine false false mark u saved input output left keyRight j width D B i right j remaining rows) := by
  have h := copyWord_eval 11 5 (by decide) (by decide) (by decide)
    (machine v p mark u saved input output left keyRight 0 width D B i right j remaining rows) rfl
  simpa only [machine_stack_11, List.length_replicate, StackRoutines.copyStacks,
    machine_stack_5, List.replicate_zero, List.append_nil, machine_update_5,
    machine_regs, read_flags, Option.getD_none, Option.isSome_none, machine_eta] using h

theorem copy_8_6 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z _width D B i right j remaining rows : ℕ) :
    Eval (copyWord 8 6) (7 * B + 5)
      (machine v p mark u saved input output left keyRight z 0 D B i right j remaining rows)
      (machine false false mark u saved input output left keyRight z B D B i right j remaining rows) := by
  have h := copyWord_eval 8 6 (by decide) (by decide) (by decide)
    (machine v p mark u saved input output left keyRight z 0 D B i right j remaining rows) rfl
  simpa only [machine_stack_8, List.length_replicate, StackRoutines.copyStacks,
    machine_stack_6, List.replicate_zero, List.append_nil, machine_update_6,
    machine_regs, read_flags, Option.getD_none, Option.isSome_none, machine_eta] using h

theorem copy_7_2 (v p mark u saved : Bool) (input output : List Bool)
    (_left keyRight z width D B i right j remaining rows : ℕ) :
    Eval (copyWord 7 2) (7 * D + 5)
      (machine v p mark u saved input output 0 keyRight z width D B i right j remaining rows)
      (machine false false mark u saved input output D keyRight z width D B i right j remaining rows) := by
  have h := copyWord_eval 7 2 (by decide) (by decide) (by decide)
    (machine v p mark u saved input output 0 keyRight z width D B i right j remaining rows) rfl
  simpa only [machine_stack_7, List.length_replicate, StackRoutines.copyStacks,
    machine_stack_2, List.replicate_zero, List.append_nil, machine_update_2,
    machine_regs, read_flags, Option.getD_none, Option.isSome_none, machine_eta] using h

theorem copy_7_10 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i _right j remaining rows : ℕ) :
    Eval (copyWord 7 10) (7 * D + 5)
      (machine v p mark u saved input output left keyRight z width D B i 0 j remaining rows)
      (machine false false mark u saved input output left keyRight z width D B i D j remaining rows) := by
  have h := copyWord_eval 7 10 (by decide) (by decide) (by decide)
    (machine v p mark u saved input output left keyRight z width D B i 0 j remaining rows) rfl
  simpa only [machine_stack_7, List.length_replicate, StackRoutines.copyStacks,
    machine_stack_10, List.replicate_zero, List.append_nil, machine_update_10,
    machine_regs, read_flags, Option.getD_none, Option.isSome_none, machine_eta] using h

theorem copy_7_12 (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j _remaining rows : ℕ) :
    Eval (copyWord 7 12) (7 * D + 5)
      (machine v p mark u saved input output left keyRight z width D B i right j 0 rows)
      (machine false false mark u saved input output left keyRight z width D B i right j D rows) := by
  have h := copyWord_eval 7 12 (by decide) (by decide) (by decide)
    (machine v p mark u saved input output left keyRight z width D B i right j 0 rows) rfl
  simpa only [machine_stack_7, List.length_replicate, StackRoutines.copyStacks,
    machine_stack_12, List.replicate_zero, List.append_nil, machine_update_12,
    machine_regs, read_flags, Option.getD_none, Option.isSome_none, machine_eta] using h

theorem set_v_machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (b : Bool) :
    Eval (atom (.set 0 b)) 1 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)
      (machine b p mark u saved input output left keyRight z width D B i right j remaining rows) := by
  simpa only [machine_regs, update_flags_zero, machine_eta] using
    atom_set_eval 0 b (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)

theorem set_mark_machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (b : Bool) :
    Eval (atom (.set 2 b)) 1 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)
      (machine v p b u saved input output left keyRight z width D B i right j remaining rows) := by
  simpa only [machine_regs, update_flags_two, machine_eta] using
    atom_set_eval 2 b (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)

theorem set_u_machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) (b : Bool) :
    Eval (atom (.set 3 b)) 1 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)
      (machine v p mark b saved input output left keyRight z width D B i right j remaining rows) := by
  simpa only [machine_regs, update_flags_three, machine_eta] using
    atom_set_eval 3 b (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)

theorem clear_i_machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    Eval (clearWord 9) (2 * i + 3) (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)
      (machine false false mark u saved input output left keyRight z width D B 0 right j remaining rows) := by
  simpa only [machine_stack_9, List.length_replicate, StackRoutines.clearStacks,
    ← List.replicate_zero (a := true), machine_update_9, machine_regs, read_flags,
    Option.getD_none, Option.isSome_none, machine_eta] using clearWord_eval 9 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)

theorem push_i_machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    Eval (pushTrue 9) 2 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)
      (machine true p mark u saved input output left keyRight z width D B (i + 1) right j remaining rows) := by
  simpa only [machine_stack_9, ← List.replicate_succ, machine_update_9,
    machine_regs, update_flags_zero, machine_eta] using pushTrue_eval 9 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)

theorem clear_j_machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    Eval (clearWord 11) (2 * j + 3) (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)
      (machine false false mark u saved input output left keyRight z width D B i right 0 remaining rows) := by
  simpa only [machine_stack_11, List.length_replicate, StackRoutines.clearStacks,
    ← List.replicate_zero (a := true), machine_update_11, machine_regs, read_flags,
    Option.getD_none, Option.isSome_none, machine_eta] using clearWord_eval 11 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)

theorem push_j_machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    Eval (pushTrue 11) 2 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)
      (machine true p mark u saved input output left keyRight z width D B i right (j + 1) remaining rows) := by
  simpa only [machine_stack_11, ← List.replicate_succ, machine_update_11,
    machine_regs, update_flags_zero, machine_eta] using pushTrue_eval 11 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)

@[simp] theorem unary_head (n : ℕ) : (unary n).head?.getD false = decide (0 < n) := by
  cases n <;> simp [unary, List.replicate_succ]
@[simp] theorem unary_present (n : ℕ) : (unary n).head?.isSome = decide (0 < n) := by
  cases n <;> simp [unary, List.replicate_succ]
@[simp] theorem unary_tail (n : ℕ) : (unary n).tail = unary (n - 1) := by
  cases n <;> rfl

theorem pop_right_machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    Eval (atom (.pop 10 0 1)) 1 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)
      (machine (decide (0 < right)) (decide (0 < right)) mark u saved input output left keyRight z width D B i (right - 1) j remaining rows) := by
  simpa only [machine_stack_10, unary_head, unary_present, unary_tail,
    machine_update_10, machine_regs, read_flags, machine_eta] using atom_pop_eval 10 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)

theorem pop_remaining_machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    Eval (atom (.pop 12 0 1)) 1 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)
      (machine (decide (0 < remaining)) (decide (0 < remaining)) mark u saved input output left keyRight z width D B i right j (remaining - 1) rows) := by
  simpa only [machine_stack_12, unary_head, unary_present, unary_tail,
    machine_update_12, machine_regs, read_flags, machine_eta] using atom_pop_eval 12 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)

theorem pop_rows_machine (v p mark u saved : Bool) (input output : List Bool)
    (left keyRight z width D B i right j remaining rows : ℕ) :
    Eval (atom (.pop 13 0 1)) 1 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)
      (machine (decide (0 < rows)) (decide (0 < rows)) mark u saved input output left keyRight z width D B i right j remaining (rows - 1)) := by
  simpa only [machine_stack_13, unary_head, unary_present, unary_tail,
    machine_update_13, machine_regs, read_flags, machine_eta] using atom_pop_eval 13 (machine v p mark u saved input output left keyRight z width D B i right j remaining rows)

def variableCost (i right j B : ℕ) (u : Bool) (coefficient : List Bool) : ℕ :=
  (7 * i + 5) + ((7 * right + 5) + ((7 * j + 5) +
    ((7 * B + 5) + preparedCost i right j B true u coefficient)))

theorem emitVariable_eval (v p u saved : Bool) (coefficient tail output : List Bool)
    (D B i right j remaining rows : ℕ) :
    Eval emitVariable (variableCost i right j B u coefficient)
      (ready v p true u saved (Encoding.frame coefficient ++ tail) output
        D B i right j remaining rows)
      (ready true false true u saved tail
        (prepend i right j B true u coefficient output) D B i right j remaining rows) := by
  let input := Encoding.frame coefficient ++ tail
  have h1 := copy_9_2 v p true u saved input output 0 0 0 0 D B i right j remaining rows
  have h2 := copy_10_4 false false true u saved input output i 0 0 0 D B i right j remaining rows
  have h3 := copy_11_5 false false true u saved input output i right 0 0 D B i right j remaining rows
  have h4 := copy_8_6 false false true u saved input output i right j 0 D B i right j remaining rows
  have h5 := prepared_machine false false true u saved coefficient tail output
    i right j D B i right j remaining rows
  exact Eval.seq h1 (Eval.seq h2 (Eval.seq h3 (Eval.seq h4 h5)))

def constantCost (D B : ℕ) (u : Bool) (coefficient : List Bool) : ℕ :=
  1 + (1 + ((7 * D + 5) + ((7 * B + 5) + preparedCost D 0 0 B false u coefficient)))

theorem emitConstant_eval (v p mark priorU u saved : Bool)
    (coefficient tail output : List Bool) (D B i right j remaining rows : ℕ) :
    Eval (emitConstant u) (constantCost D B u coefficient)
      (ready v p mark priorU saved (Encoding.frame coefficient ++ tail) output
        D B i right j remaining rows)
      (ready true false false u saved tail
        (prepend D 0 0 B false u coefficient output) D B i right j remaining rows) := by
  let input := Encoding.frame coefficient ++ tail
  have h1 := set_mark_machine v p mark priorU saved input output 0 0 0 0 D B i right j remaining rows false
  have h2 := set_u_machine v p false priorU saved input output 0 0 0 0 D B i right j remaining rows u
  have h3 := copy_7_2 v p false u saved input output 0 0 0 0 D B i right j remaining rows
  have h4 := copy_8_6 false false false u saved input output D 0 0 0 D B i right j remaining rows
  have h5 := prepared_machine false false false u saved coefficient tail output
    D 0 0 D B i right j remaining rows
  exact Eval.seq h1 (Eval.seq h2 (Eval.seq h3 (Eval.seq h4 h5)))

def frames (coefficients : List (List Bool)) : List Bool := coefficients.flatMap Encoding.frame

@[simp] theorem frames_nil : frames [] = [] := rfl
@[simp] theorem frames_cons (c : List Bool) (cs : List (List Bool)) :
    frames (c :: cs) = Encoding.frame c ++ frames cs := rfl

def columnOutput (B i j : ℕ) (u : Bool) : List (List Bool) → List Bool → List Bool
  | [], output => output
  | c :: cs, output => columnOutput B (i + 1) j u cs
      (prepend i cs.length j B true u c output)

def columnCost (B i j : ℕ) (u : Bool) : List (List Bool) → ℕ
  | [] => 1
  | c :: cs => (variableCost i cs.length j B u c + 4) + columnCost B (i + 1) j u cs + 1

theorem columnBody_eval (u saved : Bool) (coefficient tail output : List Bool)
    (D B i j remaining rows : ℕ) :
    Eval columnBody (variableCost i remaining j B u coefficient + 4)
      (ready true true true u saved (Encoding.frame coefficient ++ tail) output
        D B i remaining j remaining rows)
      (ready (decide (0 < remaining)) (decide (0 < remaining)) true u saved tail
        (prepend i remaining j B true u coefficient output)
        D B (i + 1) (remaining - 1) j (remaining - 1) rows) := by
  let output' := prepend i remaining j B true u coefficient output
  have h1 := emitVariable_eval true true u saved coefficient tail output D B i remaining j remaining rows
  have h2 := push_i_machine true false true u saved tail output' 0 0 0 0 D B i remaining j remaining rows
  have h3 := pop_right_machine true false true u saved tail output' 0 0 0 0 D B (i+1) remaining j remaining rows
  have h4 := pop_remaining_machine (decide (0 < remaining)) (decide (0 < remaining))
    true u saved tail output' 0 0 0 0 D B (i+1) (remaining-1) j remaining rows
  exact Eval.seq h1 (Eval.seq h2 (Eval.seq h3 h4))

/-- The runtime column loop emits exactly one term for each framed coefficient.
All three per-column work counters are cleared when the loop exits. -/
theorem columnLoop_eval (cs : List (List Bool)) (u saved : Bool)
    (tail output : List Bool) (D B i j rows : ℕ) :
    Eval columnLoop (columnCost B i j u cs)
      (ready (decide (0 < cs.length)) (decide (0 < cs.length)) true u saved
        (frames cs ++ tail) output D B i (cs.length - 1) j (cs.length - 1) rows)
      (ready false false true u saved tail (columnOutput B i j u cs output)
        D B (i + cs.length) 0 j 0 rows) := by
  induction cs generalizing i output with
  | nil => simpa [columnCost, columnOutput] using
      (Eval.while_false (body := columnBody)
        (a := ready false false true u saved tail output D B i 0 j 0 rows) (test := (1 : Fin 5)) rfl)
  | cons c cs ih =>
    have hb := columnBody_eval u saved c (frames cs ++ tail) output D B i j cs.length rows
    have hr := ih (output := prepend i cs.length j B true u c output) (i := i+1)
    have h := Eval.while_true (test := (1 : Fin 5)) rfl hb hr
    simpa [columnLoop, columnCost, columnOutput,
      List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

def rowCost (D B i j : ℕ) (u : Bool) (cs : List (List Bool)) : ℕ :=
  (2 * i + 3) + ((7 * D + 5) + (1 + ((7 * D + 5) +
    (1 + (columnCost B 0 j u cs + (2 + (1 + 1)))))))

variable {D : ℕ}

theorem rowBody_eval (cs : List (List Bool)) (hcs : cs.length = D)
    (u saved : Bool) (tail output : List Bool) (B i j rows : ℕ) :
    Eval rowBody (rowCost D B i j u cs)
      (ready true true true u saved (frames cs ++ tail) output D B i 0 j 0 rows)
      (ready (decide (0 < rows)) (decide (0 < rows)) true false saved tail
        (columnOutput B 0 j u cs output) D B D 0 (j + 1) 0 (rows - 1)) := by
  let input := frames cs ++ tail
  let output' := columnOutput B 0 j u cs output
  have h1 := clear_i_machine true true true u saved input output 0 0 0 0 D B i 0 j 0 rows
  have h2 := copy_7_10 false false true u saved input output 0 0 0 0 D B 0 0 j 0 rows
  have h3 := pop_right_machine false false true u saved input output 0 0 0 0 D B 0 D j 0 rows
  have h4 := copy_7_12 (decide (0 < D)) (decide (0 < D)) true u saved input output 0 0 0 0
    D B 0 (D-1) j 0 rows
  have h5 := pop_remaining_machine false false true u saved input output 0 0 0 0
    D B 0 (D-1) j D rows
  have h6 := columnLoop_eval cs u saved tail output D B 0 j rows
  simp only [hcs, Nat.zero_add] at h6
  have h7 := push_j_machine false false true u saved tail output' 0 0 0 0 D B D 0 j 0 rows
  have h8 := set_u_machine true false true u saved tail output' 0 0 0 0 D B D 0 (j+1) 0 rows false
  have h9 := pop_rows_machine true false true false saved tail output' 0 0 0 0 D B D 0 (j+1) 0 rows
  exact Eval.seq h1 (Eval.seq h2 (Eval.seq h3 (Eval.seq h4 (Eval.seq h5
    (Eval.seq h6 (Eval.seq h7 (Eval.seq h8 h9)))))))

def rowsFrames (rows : List (List (List Bool))) : List Bool := rows.flatMap frames

@[simp] theorem rowsFrames_nil : rowsFrames [] = [] := rfl
@[simp] theorem rowsFrames_cons (cs : List (List Bool)) (rss : List (List (List Bool))) :
    rowsFrames (cs :: rss) = frames cs ++ rowsFrames rss := rfl

def rowsOutput (B j : ℕ) (u : Bool) : List (List (List Bool)) → List Bool → List Bool
  | [], output => output
  | cs :: rss, output => rowsOutput B (j+1) false rss (columnOutput B 0 j u cs output)

def rowsCost (D B i j : ℕ) (u : Bool) : List (List (List Bool)) → ℕ
  | [] => 1
  | cs :: rss => rowCost D B i j u cs + rowsCost D B D (j+1) false rss + 1

def finalColumn (D i : ℕ) (rss : List (List (List Bool))) : ℕ :=
  if rss = [] then i else D

/-- The runtime row loop consumes the complete rectangular stream.  Only the
first row uses U; subsequent rows use the increasing Z counter. -/
theorem rowLoop_eval (rss : List (List (List Bool))) (hrows : ∀ cs ∈ rss, cs.length = D)
    (u saved : Bool) (tail output : List Bool) (B i j : ℕ) :
    Eval rowLoop (rowsCost D B i j u rss)
      (ready (decide (0 < rss.length)) (decide (0 < rss.length)) true u saved
        (rowsFrames rss ++ tail) output D B i 0 j 0 (rss.length - 1))
      (ready false false true (if rss = [] then u else false) saved tail
        (rowsOutput B j u rss output) D B (finalColumn D i rss) 0 (j + rss.length) 0 0) := by
  induction rss generalizing i j u output with
  | nil =>
    simpa [rowsCost, rowsOutput, finalColumn] using
      (Eval.while_false (body := rowBody)
        (a := ready false false true u saved tail output D B i 0 j 0 0) (test := (1 : Fin 5)) rfl)
  | cons cs rss ih =>
    have hcs : cs.length = D := hrows cs (by simp)
    have htail : ∀ row ∈ rss, row.length = D := fun row hr => hrows row (by simp [hr])
    have hb := rowBody_eval cs hcs u saved (rowsFrames rss ++ tail) output B i j rss.length
    have hr := ih htail (u := false) (output := columnOutput B 0 j u cs output) (i := D) (j := j+1)
    have h := Eval.while_true (test := (1 : Fin 5)) rfl hb hr
    simpa [rowLoop, rowsCost, rowsOutput, finalColumn,
      List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

def argumentOutput (D B : ℕ) (beta negBeta : List Bool)
    (rss : List (List (List Bool))) (output : List Bool) : List Bool :=
  rowsOutput B 0 true rss
    (prepend D 0 0 B false true negBeta (prepend D 0 0 B false false beta output))

def argumentCost (D B : ℕ) (beta negBeta : List Bool)
    (rss : List (List (List Bool))) : ℕ :=
  constantCost D B false beta + (constantCost D B true negBeta +
    (1 + (1 + (1 + (rowsCost D B 0 0 true rss +
      ((2 * finalColumn D 0 rss + 3) + (2 * rss.length + 3)))))))

/-- Fixed-control execution from the two constant coefficient records and the
rectangular Taylor records. The negative-beta word is a coefficient-ring input
record; no ring arithmetic is hidden in this serializer. -/
theorem command_eval (rss : List (List (List Bool))) (hrows : ∀ cs ∈ rss, cs.length = D)
    (v p mark priorU saved : Bool) (beta negBeta tail output : List Bool) (B : ℕ) :
    Eval command (argumentCost D B beta negBeta rss)
      (ready v p mark priorU saved
        (Encoding.frame beta ++ (Encoding.frame negBeta ++ (rowsFrames rss ++ tail)))
        output D B 0 0 0 0 rss.length)
      (ready false false true (if rss = [] then true else false) saved tail
        (argumentOutput D B beta negBeta rss output) D B 0 0 0 0 0) := by
  let output1 := prepend D 0 0 B false false beta output
  let output2 := prepend D 0 0 B false true negBeta output1
  let output3 := rowsOutput B 0 true rss output2
  let tail1 := Encoding.frame negBeta ++ (rowsFrames rss ++ tail)
  let tail2 := rowsFrames rss ++ tail
  have h1 := emitConstant_eval v p mark priorU false saved beta tail1 output D B 0 0 0 0 rss.length
  have h2 := emitConstant_eval true false false false true saved negBeta tail2 output1 D B 0 0 0 0 rss.length
  have h3 := set_mark_machine true false false true saved tail2 output2 0 0 0 0 D B 0 0 0 0 rss.length true
  have h4 := set_u_machine true false true true saved tail2 output2 0 0 0 0 D B 0 0 0 0 rss.length true
  have h5 := pop_rows_machine true false true true saved tail2 output2 0 0 0 0 D B 0 0 0 0 rss.length
  have h6 := rowLoop_eval rss hrows true saved tail output2 B 0 0
  simp only [Nat.zero_add] at h6
  have h7 := clear_i_machine false false true (if rss = [] then true else false) saved
    tail output3 0 0 0 0 D B (finalColumn D 0 rss) 0 rss.length 0 0
  have h8 := clear_j_machine false false true (if rss = [] then true else false) saved
    tail output3 0 0 0 0 D B 0 0 rss.length 0 0
  exact Eval.seq h1 (Eval.seq h2 (Eval.seq h3 (Eval.seq h4 (Eval.seq h5
    (Eval.seq h6 (Eval.seq h7 h8))))))

/-- The concrete finite instruction table, not only its structured syntax,
serializes every coefficient and returns with all per-loop scratch counters empty. -/
theorem program_trace (rss : List (List (List Bool))) (hrows : ∀ cs ∈ rss, cs.length = D)
    (v p mark priorU saved : Bool) (beta negBeta tail output : List Bool) (B : ℕ) :
    Trace program (argumentCost D B beta negBeta rss + 1)
      ((ready v p mark priorU saved
        (Encoding.frame beta ++ (Encoding.frame negBeta ++ (rowsFrames rss ++ tail)))
        output D B 0 0 0 0 rss.length).withPC (some program.entry))
      ((ready false false true (if rss = [] then true else false) saved tail
        (argumentOutput D B beta negBeta rss output) D B 0 0 0 0 0).withPC none) :=
  StructuredCalls.compiled_halt_trace
    (command_eval rss hrows v p mark priorU saved beta negBeta tail output B) 0 3

/-- Total coefficient payload bits, independent of the framing overhead. -/
def payloadBits (cs : List (List Bool)) : ℕ := (cs.map List.length).sum

def rowsPayloadBits (rss : List (List (List Bool))) : ℕ := (rss.map payloadBits).sum

theorem rawKey_length_le (left right j : ℕ) (mark u : Bool) :
    (SubexpArgumentKeyEmitter.rawKey left right j mark u).length ≤ left + right + j + 5 := by
  cases mark <;> cases u <;>
    simp [SubexpArgumentKeyEmitter.rawKey, SubexpArgumentKeyEmitter.markBits,
      SubexpArgumentKeyEmitter.uBits] <;> omega

theorem preparedCost_le (left right j B : ℕ) (mark u : Bool) (c : List Bool) :
    preparedCost left right j B mark u c ≤
      29 * c.length + 26 * (left + right + j) + 25 * B + 183 := by
  have hr := SubexpArgumentKeyEmitter.rawCost_le left right j mark u
  have hl := rawKey_length_le left right j mark u
  have hd : B - (SubexpArgumentKeyEmitter.rawKey left right j mark u).length ≤ B := Nat.sub_le _ _
  simp only [preparedCost, SubexpArgumentKeyEmitter.paddedKey,
    List.length_append, List.length_replicate]
  omega

theorem variableCost_le (i right j B : ℕ) (u : Bool) (c : List Bool) :
    variableCost i right j B u c ≤
      29 * c.length + 33 * (i + right + j) + 32 * B + 203 := by
  have h := preparedCost_le i right j B true u c
  unfold variableCost
  omega

theorem constantCost_le (D B : ℕ) (u : Bool) (c : List Bool) :
    constantCost D B u c ≤ 29 * c.length + 33 * D + 32 * B + 195 := by
  have h := preparedCost_le D 0 0 B false u c
  unfold constantCost
  omega

theorem columnCost_le (cs : List (List Bool)) (B i j : ℕ) (u : Bool) :
    columnCost B i j u cs ≤ 29 * payloadBits cs +
      cs.length * (33 * (i + cs.length + j) + 32 * B + 208) + 1 := by
  induction cs generalizing i with
  | nil => simp [columnCost, payloadBits]
  | cons c cs ih =>
    have hv := variableCost_le i cs.length j B u c
    have ht := ih (i+1)
    simp only [columnCost, payloadBits, List.map_cons, List.sum_cons,
      List.length_cons] at *
    nlinarith

theorem rowCost_le (cs : List (List Bool)) (hcs : cs.length = D)
    (B i j : ℕ) (u : Bool) (hi : i ≤ D) :
    rowCost D B i j u cs ≤ 29 * payloadBits cs +
      D * (33 * (D + j) + 32 * B + 224) + 20 := by
  have hc := columnCost_le cs B 0 j u
  rw [hcs] at hc
  unfold rowCost
  nlinarith

theorem rowsCost_le (rss : List (List (List Bool)))
    (hrows : ∀ cs ∈ rss, cs.length = D) (B i j : ℕ) (u : Bool) (hi : i ≤ D) :
    rowsCost D B i j u rss ≤ 29 * rowsPayloadBits rss +
      rss.length * (D * (33 * (D + j + rss.length) + 32 * B + 224) + 21) + 1 := by
  induction rss generalizing i j u with
  | nil => simp [rowsCost, rowsPayloadBits]
  | cons cs rss ih =>
    have hcs : cs.length = D := hrows cs (by simp)
    have htail : ∀ row ∈ rss, row.length = D := fun row hr => hrows row (by simp [hr])
    have hc := rowCost_le cs hcs B i j u hi
    have ht := ih htail D (j+1) false (le_refl D)
    simp only [rowsCost, rowsPayloadBits, List.map_cons, List.sum_cons,
      List.length_cons] at *
    nlinarith [Nat.zero_le (D * rss.length)]

theorem argumentCost_le (rss : List (List (List Bool)))
    (hrows : ∀ cs ∈ rss, cs.length = D) (B : ℕ) (beta negBeta : List Bool) :
    argumentCost D B beta negBeta rss + 1 ≤
      29 * (beta.length + negBeta.length + rowsPayloadBits rss) +
      68 * D + 64 * B + 401 +
      rss.length * (D * (33 * (D + rss.length) + 32 * B + 224) + 23) := by
  have hb := constantCost_le D B false beta
  have hn := constantCost_le D B true negBeta
  have hr := rowsCost_le rss hrows B 0 0 true (Nat.zero_le D)
  have hf : finalColumn D 0 rss ≤ D := by
    unfold finalColumn
    split <;> omega
  unfold argumentCost
  nlinarith

end SubexponentialSAT.SubexpArgumentEmitLoop

end OAI.Algorithms
