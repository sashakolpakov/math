import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# A fixed word-to-constant-quartic marshaler

The base word is on stack 0 and the width shape on stack 1. The program
preserves the shape, appends three zero words to the base word, and clears
all three scratch stacks. Only Boolean stack instructions are executed.
-/

namespace SubexponentialSAT.SubexpQuarticMarshal

open BitProgram ProgramLinking StackRoutines ListRegisterProgram

abbrev Regs := Fin 3 → Bool

def registerState (bit present zero : Bool) : Regs := ![bit, present, zero]

def stackState (word shape aux counter temp : List Bool) : Fin 5 → List Bool :=
  ![word, shape, aux, counter, temp]

@[simp] theorem register_zero (b p z : Bool) : registerState b p z 0 = b := rfl
@[simp] theorem register_one (b p z : Bool) : registerState b p z 1 = p := rfl
@[simp] theorem register_two (b p z : Bool) : registerState b p z 2 = z := rfl

@[simp] theorem update_register_zero (b p z v : Bool) :
    Function.update (registerState b p z) 0 v = registerState v p z := by
  funext i; fin_cases i <;> simp [registerState]

@[simp] theorem update_register_one (b p z v : Bool) :
    Function.update (registerState b p z) 1 v = registerState b v z := by
  funext i; fin_cases i <;> simp [registerState]

@[simp] theorem update_register_two (r : Regs) :
    Function.update r 2 false = registerState (r 0) (r 1) false := by
  funext i; fin_cases i <;> simp [registerState]

@[simp] theorem stack_word (w s a c t : List Bool) : stackState w s a c t 0 = w := rfl
@[simp] theorem stack_shape (w s a c t : List Bool) : stackState w s a c t 1 = s := rfl
@[simp] theorem stack_aux (w s a c t : List Bool) : stackState w s a c t 2 = a := rfl
@[simp] theorem stack_counter (w s a c t : List Bool) : stackState w s a c t 3 = c := rfl
@[simp] theorem stack_temp (w s a c t : List Bool) : stackState w s a c t 4 = t := rfl

@[simp] theorem update_word (w s a c t next : List Bool) :
    Function.update (stackState w s a c t) 0 next = stackState next s a c t := by
  funext i; fin_cases i <;> simp [stackState]

@[simp] theorem update_counter (w s a c t next : List Bool) :
    Function.update (stackState w s a c t) 3 next = stackState w s a next t := by
  funext i; fin_cases i <;> simp [stackState]

/-- Each shape cell produces exactly three zero bits. -/
abbrev zeroProgram : Program 3 5 7 where
  inputStack := 3
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .set 2 false 1
    | 1 => .pop 3 0 1 2
    | 2 => .branch 1 3 6
    | 3 => .push 0 2 4
    | 4 => .push 0 2 5
    | 5 => .push 0 2 1
    | _ => .halt

def zeroCfg (pc : Option (Fin 7)) (b p : Bool)
    (word shape aux counter : List Bool) : Cfg 3 5 7 :=
  ⟨pc, registerState b p false, stackState word shape aux counter []⟩

theorem zero_round (b p a : Bool) (word shape aux counter : List Bool) :
    Trace zeroProgram 5
      (zeroCfg (some 1) b p word shape aux (a :: counter))
      (zeroCfg (some 1) a true (false :: false :: false :: word) shape aux counter) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, zeroProgram, zeroCfg, execInstr, readRegs]

theorem zero_exit (b p : Bool) (word shape aux : List Bool) :
    Trace zeroProgram 3 (zeroCfg (some 1) b p word shape aux [])
      (zeroCfg none false false word shape aux []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, zeroProgram, zeroCfg, execInstr, readRegs]

theorem zero_loop (counter : List Bool) (b p : Bool) (word shape aux : List Bool) :
    Trace zeroProgram (5 * counter.length + 3)
      (zeroCfg (some 1) b p word shape aux counter)
      (zeroCfg none false false
        (List.replicate (3 * counter.length) false ++ word) shape aux []) := by
  induction counter generalizing b p word with
  | nil => simpa using zero_exit b p word shape aux
  | cons a counter ih =>
      have ht := (zero_round b p a word shape aux counter).trans
        (ih a true (false :: false :: false :: word))
      have hc : 5 + (5 * counter.length + 3) = 5 * (counter.length + 1) + 3 := by omega
      rw [hc] at ht
      have hpad : List.replicate (3 * counter.length) false ++
          (false :: false :: false :: word) =
          List.replicate (3 * (counter.length + 1)) false ++ word := by
        change List.replicate (3 * counter.length) false ++
          (List.replicate 3 false ++ word) = _
        rw [← List.append_assoc, ← List.replicate_add]
        have hn : 3 * counter.length + 3 = 3 * (counter.length + 1) := by omega
        rw [hn]
      rw [hpad] at ht
      exact ht

theorem zero_run (r : Regs) (word shape aux counter : List Bool) :
    Run zeroProgram (5 * counter.length + 4) r (stackState word shape aux counter [])
      (registerState false false false)
      (stackState (List.replicate (3 * counter.length) false ++ word) shape aux [] []) := by
  have hs : Trace zeroProgram 1
      ⟨some 0, r, stackState word shape aux counter []⟩
      (zeroCfg (some 1) (r 0) (r 1) word shape aux counter) := by
    apply Computation.Trace.cons _ (Computation.Trace.refl _)
    simp [step, zeroCfg, execInstr]
  have ht := hs.trans (zero_loop counter (r 0) (r 1) word shape aux)
  have hc : 1 + (5 * counter.length + 3) = 5 * counter.length + 4 := by omega
  rw [hc] at ht
  exact ht

abbrev copyWidth : Program 3 5 8 := copyProgram 1 3 4 0 1
abbrev storeWord : Program 3 5 4 := transferProgram 0 2 0 1
abbrev restoreWord : Program 3 5 4 := transferProgram 2 0 0 1

/-- The whole instruction table has 23 labels, for every word and width. -/
abbrev program : Program 3 5 23 :=
  link (link (link copyWidth storeWord) zeroProgram) restoreWord

def marshalBits (word shape : List Bool) : List Bool :=
  word ++ List.replicate (3 * shape.length) false

private theorem copy_width_state (word shape : List Bool) :
    copyStacks (1 : Fin 5) 3 (stackState word shape [] [] []) =
      stackState word shape [] shape [] := by
  funext i; fin_cases i <;> simp [copyStacks, stackState]

private theorem store_word_state (word shape : List Bool) :
    transferStacks (0 : Fin 5) 2 (stackState word shape [] shape []) =
      stackState [] shape word.reverse shape [] := by
  funext i; fin_cases i <;> simp [transferStacks, stackState]

private theorem restore_word_state (word shape : List Bool) :
    transferStacks (2 : Fin 5) 0
      (stackState (List.replicate (3 * shape.length) false) shape word.reverse [] []) =
      stackState (marshalBits word shape) shape [] [] [] := by
  funext i; fin_cases i <;> simp [transferStacks, stackState, marshalBits]

/-- Exact instruction count. No relationship between word and shape lengths
is required for the padding operation itself. -/
theorem run (r : Regs) (word shape : List Bool) :
    ∃ rf, Run program (6 * word.length + 12 * shape.length + 15)
      r (stackState word shape [] [] [])
      rf (stackState (marshalBits word shape) shape [] [] []) := by
  let r₁ := readRegs r 0 1 none
  let r₂ := readRegs r₁ 0 1 none
  let r₃ := registerState false false false
  let r₄ := readRegs r₃ 0 1 none
  have h1 : Run copyWidth (7 * shape.length + 5)
      r (stackState word shape [] [] []) r₁ (stackState word shape [] shape []) := by
    have h := copy_run (1 : Fin 5) 3 4 (0 : Fin 3) 1
      (by decide) (by decide) (by decide) (by decide)
      r (stackState word shape [] [] []) rfl
    simpa only [copy_width_state, stack_shape] using h
  have h2 : Run storeWord (3 * word.length + 3)
      r₁ (stackState word shape [] shape []) r₂ (stackState [] shape word.reverse shape []) := by
    have h := transfer_run (0 : Fin 5) 2 (0 : Fin 3) 1
      (by decide) (by decide) r₁ (stackState word shape [] shape [])
    simpa only [store_word_state, stack_word] using h
  have h3 : Run zeroProgram (5 * shape.length + 4)
      r₂ (stackState [] shape word.reverse shape [])
      r₃ (stackState (List.replicate (3 * shape.length) false) shape word.reverse [] []) := by
    simpa using zero_run r₂ [] shape word.reverse shape
  have h4 : Run restoreWord (3 * word.length + 3)
      r₃ (stackState (List.replicate (3 * shape.length) false) shape word.reverse [] [])
      r₄ (stackState (marshalBits word shape) shape [] [] []) := by
    have h := transfer_run (2 : Fin 5) 0 (0 : Fin 3) 1
      (by decide) (by decide) r₃
      (stackState (List.replicate (3 * shape.length) false) shape word.reverse [] [])
    simpa only [restore_word_state, stack_aux, List.length_reverse] using h
  have ht := link_run _ _ (link_run _ _ (link_run _ _ h1 h2) h3) h4
  have hc : ((7 * shape.length + 5) + (3 * word.length + 3) +
      (5 * shape.length + 4)) + (3 * word.length + 3) =
      6 * word.length + 12 * shape.length + 15 := by omega
  rw [hc] at ht
  exact ⟨r₄, ht⟩

theorem marshalBits_length (word shape : List Bool) (B : ℕ)
    (hw : word.length = B) (hs : shape.length = B) :
    (marshalBits word shape).length = 4 * B := by
  simp only [marshalBits, List.length_append, List.length_replicate, hw, hs]
  omega

/-- Convenient equal-width bound for the four-coordinate payload. -/
theorem run_bound (r : Regs) (word shape : List Bool) (B : ℕ)
    (hw : word.length = B) (hs : shape.length = B) :
    ∃ rf, BitProgram.RunsIn program (20 * B + 30)
      ⟨some program.entry, r, stackState word shape [] [] []⟩
      ⟨none, rf, stackState (marshalBits word shape) shape [] [] []⟩ := by
  obtain ⟨rf, ht⟩ := run r word shape
  refine ⟨rf, _, ?_, ht⟩
  rw [hw, hs]
  omega

theorem primitive_run (r : Regs) (word shape : List Bool) (B : ℕ)
    (hw : word.length = B) (hs : shape.length = B) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (20 * B + 30))
      (BitProgram.primitiveCfg program
        ⟨some program.entry, r, stackState word shape [] [] []⟩)
      (BitProgram.primitiveCfg program
        ⟨none, rf, stackState (marshalBits word shape) shape [] [] []⟩) := by
  obtain ⟨rf, ht⟩ := run_bound r word shape B hw hs
  exact ⟨rf, BitProgram.primitive_execution program ht⟩

end SubexponentialSAT.SubexpQuarticMarshal

end OAI.Algorithms
