import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.CounterPrograms

namespace OAI.Algorithms

/-!
# Loading one statically selected search width

For fixed k and d, the code writes d to the current-width stack and copies the
corresponding threshold bank entry. The table index is fixed in the emitted
program; its value remains runtime data. Previously stored width/threshold
words are explicitly cleared and charged.
-/

namespace SubexponentialSAT.ExecCNFWidthLoad

open BitProgram StructuredCalls

abbrev Data (k : ℕ) := State 32 (k + 34)
abbrev Code (k : ℕ) := Cmd 32 (k + 34)

def low (k : ℕ) (i : Fin 32) : Fin (k + 34) := ⟨i.val, by omega⟩
def bank (k d : ℕ) (hd : d ≤ k) : Fin (k + 34) := ⟨33 + d, by omega⟩

theorem low_injective (k : ℕ) : Function.Injective (low k) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin (k + 34) => x.val) h

def reg (i : Fin 8) : Fin 32 := Fin.castAdd 24 i
theorem reg_injective : Function.Injective reg := Fin.castAdd_injective 8 24

def clear (k : ℕ) (port : Fin (k + 34)) : Code k :=
  .call (StackRoutines.clearProgram port 0 1)

abbrev cleared {k : ℕ} (port : Fin (k + 34)) (d : Data k) : Data k :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

theorem clear_eval {k : ℕ} (port : Fin (k + 34)) (d : Data k) :
    Eval (clear k port) (2 * (d.stacks port).length + 3) d (cleared port d) :=
  .call _ (ListRegisterProgram.clear_run port 0 1 d.regs d.stacks)

def writeWidth (k d : ℕ) : Code k :=
  liftCommand (ArithmeticExpressionSupport.pushWord (low k 14) d.bits)
    (low k 14) (low k 14) reg id

theorem writeWidth_eval (k d : ℕ) (a : Data k) (h14 : a.stacks (low k 14) = []) :
    ∃ b, Eval (writeWidth k d) (2 * d.bits.length + 1) a b ∧
      b.stacks = Function.update a.stacks (low k 14) d.bits := by
  obtain ⟨rf, he⟩ := ArithmeticExpressionSupport.pushWord_eval
    (low k 14) d.bits (projectState reg id a)
  let b := embedState reg id a
    ⟨rf, Function.update (projectState reg id a).stacks (low k 14)
      (d.bits ++ (projectState reg id a).stacks (low k 14))⟩
  refine ⟨b, eval_liftCommand_from_state _ _ _ reg id a reg_injective
    Function.injective_id he, ?_⟩
  funext i
  have hp := embedState_stack reg id a
    (⟨rf, Function.update (projectState reg id a).stacks (low k 14)
      (d.bits ++ (projectState reg id a).stacks (low k 14))⟩ : State 8 (k + 34))
    Function.injective_id i
  simpa [b, projectState, h14] using hp

def copyThreshold (k d : ℕ) (hd : d ≤ k) : Code k :=
  .call (StackRoutines.copyProgram (bank k d hd) (low k 15) (low k 25) 0 1)

abbrev copiedThreshold {k : ℕ} (d : ℕ) (hd : d ≤ k) (a : Data k) : Data k :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks (bank k d hd) (low k 15) a.stacks⟩

theorem bank_ne_low (k d : ℕ) (hd : d ≤ k) (i : Fin 32) :
    bank k d hd ≠ low k i := by
  intro h
  have he := congrArg Fin.val h
  simp only [bank, low] at he
  omega

theorem copyThreshold_eval (k d : ℕ) (hd : d ≤ k) (a : Data k)
    (h25 : a.stacks (low k 25) = []) :
    Eval (copyThreshold k d hd) (7 * (a.stacks (bank k d hd)).length + 5)
      a (copiedThreshold d hd a) := by
  apply Eval.call
  exact ListRegisterProgram.copy_run (bank k d hd) (low k 15) (low k 25) 0 1
    (bank_ne_low k d hd 15) (bank_ne_low k d hd 25)
    (by intro h; have he := congrArg Fin.val h; change (25 : ℕ) = 15 at he; omega)
    (by decide) a.regs a.stacks h25

abbrev command (k d : ℕ) (hd : d ≤ k) : Code k :=
  .seq (clear k (low k 14)) (.seq (clear k (low k 15))
    (.seq (writeWidth k d) (copyThreshold k d hd)))

def bound (k d : ℕ) (hd : d ≤ k) (a : Data k) : ℕ :=
  2 * (a.stacks (low k 14)).length + 2 * (a.stacks (low k 15)).length +
    2 * d.bits.length + 7 * (a.stacks (bank k d hd)).length + 12

/-- Both loaded words and preservation of every other stack follow from
actual finite-code execution. -/
theorem command_eval (k d : ℕ) (hd : d ≤ k) (a : Data k)
    (h25 : a.stacks (low k 25) = []) :
    ∃ b, Eval (command k d hd) (bound k d hd a) a b ∧
      b.stacks (low k 14) = d.bits ∧
      b.stacks (low k 15) = a.stacks (bank k d hd) ∧
      (∀ i, i ≠ low k 14 → i ≠ low k 15 → b.stacks i = a.stacks i) := by
  let b := cleared (low k 14) a
  let c := cleared (low k 15) b
  have h1415 : low k 14 ≠ low k 15 := (low_injective k).ne (by decide)
  have hc14 : c.stacks (low k 14) = [] := by
    simp [c, b, StackRoutines.clearStacks, h1415]
  obtain ⟨e, he, hes⟩ := writeWidth_eval k d c hc14
  have he25 : e.stacks (low k 25) = [] := by
    rw [hes]
    simpa [c, b, cleared, StackRoutines.clearStacks, low, Function.update_apply] using h25
  have he15 : e.stacks (low k 15) = [] := by
    simp [hes, c, StackRoutines.clearStacks, h1415.symm]
  have hebank : e.stacks (bank k d hd) = a.stacks (bank k d hd) := by
    simp [hes, c, b, StackRoutines.clearStacks,
      bank_ne_low k d hd 14, bank_ne_low k d hd 15]
  have hb15 : b.stacks (low k 15) = a.stacks (low k 15) := by
    simp [b, StackRoutines.clearStacks, h1415.symm]
  refine ⟨copiedThreshold d hd e, ?_, ?_, ?_, ?_⟩
  · have ht := Eval.seq (clear_eval (low k 14) a)
      (Eval.seq (clear_eval (low k 15) b)
        (Eval.seq he (copyThreshold_eval k d hd e he25)))
    have hc : (2 * (a.stacks (low k 14)).length + 3) +
        ((2 * (b.stacks (low k 15)).length + 3) +
          ((2 * d.bits.length + 1) + (7 * (e.stacks (bank k d hd)).length + 5))) =
        bound k d hd a := by rw [hb15, hebank]; unfold bound; omega
    simpa only [hc] using ht
  · simp [ StackRoutines.copyStacks, h1415, hes]
  · simp [ StackRoutines.copyStacks, he15, hebank]
  · intro i hi14 hi15
    simp [ StackRoutines.copyStacks, hes, c, b, StackRoutines.clearStacks, hi14, hi15]

theorem width_value (d : ℕ) : CounterPrograms.value d.bits = d := by
  rw [CounterPrograms.value_eq_toNat, ArithmeticExpressionSupport.bits_value]

abbrev program (k d : ℕ) (hd : d ≤ k) :=
  compiled (command k d hd) (bank k d hd) (low k 15)

theorem program_runs (k d : ℕ) (hd : d ≤ k) (a : Data k)
    (h25 : a.stacks (low k 25) = []) :
    ∃ b : Data k, RunsIn (program k d hd) (bound k d hd a + 1)
      (a.withPC (some (program k d hd).entry)) (b.withPC none) ∧
      b.stacks (low k 14) = d.bits ∧ b.stacks (low k 15) = a.stacks (bank k d hd) ∧
      (∀ i, i ≠ low k 14 → i ≠ low k 15 → b.stacks i = a.stacks i) := by
  obtain ⟨b, he, h14, h15, hf⟩ := command_eval k d hd a h25
  exact ⟨b, ⟨bound k d hd a + 1, le_rfl,
    compiled_halt_trace he (bank k d hd) (low k 15)⟩, h14, h15, hf⟩

end SubexponentialSAT.ExecCNFWidthLoad

end OAI.Algorithms
