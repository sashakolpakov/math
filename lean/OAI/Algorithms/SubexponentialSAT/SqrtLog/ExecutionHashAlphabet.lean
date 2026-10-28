import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAlphabetProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! A paid, runtime-sized alphabet for the sparse-hash selector.  The existing
binary countdown emits all words below the supplied count; this wrapper also
clears its padded counter.  No instruction table depends on the count or word
width.  Only the six explicitly mapped stacks can change. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashAlphabet

open BitProgram StructuredCalls

abbrev command : Cmd 6 6 :=
  .seq (.call SubexpAlphabetProgram.program)
    (.call (StackRoutines.clearProgram 0 0 1))

def budget (count width : ℕ) : ℕ :=
  (count + 1) * (60 * width + 60) + 2 * width + 3

theorem command_eval (word : List Bool) (regs : Fin 6 → Bool) :
    ∃ t ≤ budget (CounterPrograms.value word) word.length,
      ∃ e : State 6 6,
        Eval command t (SubexpAlphabetProgram.inputState word regs) e ∧
        e.stacks 5 = ProgramEncoding.encodeRecords (SubexpAlphabetProgram.alphabetWords word) ∧
        (∀ i : Fin 6, i ≠ 5 → e.stacks i = []) := by
  obtain ⟨a, hout, hc, h1, _, hlen, t, ht, htrace⟩ :=
    SubexpAlphabetProgram.program_runsIn_clean word regs
  let e : State 6 6 :=
    ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 0 a.stacks⟩
  have he := Subexp.TupleProgram.clear_eval (0 : Fin 6) (0 : Fin 6) 1 a
  refine ⟨t + (2 * (a.stacks 0).length + 3), ?_, e,
    (Eval.call _ htrace).seq he, ?_, ?_⟩
  · rw [hlen]
    dsimp [budget]
    omega
  · simpa [e, StackRoutines.clearStacks] using hout
  · intro i hi
    rcases hc with ⟨h2, h3, h4⟩
    fin_cases i <;> simp_all [e, StackRoutines.clearStacks]

structure Ports (R S : ℕ) where
  register : Fin 6 → Fin R
  stack : Fin 6 → Fin S
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

abbrev generate {R S : ℕ} (p : Ports R S) : Cmd R S :=
  liftCommand command 0 5 p.register p.stack

/-- The binary count on port0 is consumed and all work ports are cleaned.
The complete framed alphabet is produced on port5; every other caller stack
and register is preserved literally. -/
theorem generate_eval {R S : ℕ} (p : Ports R S) (a : State R S)
    (empty : ∀ i : Fin 6, i ≠ 0 → a.stacks (p.stack i) = []) :
    ∃ t ≤ budget (CounterPrograms.value (a.stacks (p.stack 0)))
        (a.stacks (p.stack 0)).length + 1,
      ∃ e : State R S, Eval (generate p) t a e ∧
        e.stacks (p.stack 5) = ProgramEncoding.encodeRecords
          (SubexpAlphabetProgram.alphabetWords (a.stacks (p.stack 0))) ∧
        (∀ i : Fin 6, i ≠ 5 → e.stacks (p.stack i) = []) ∧
        (∀ i, (∀ j, p.stack j ≠ i) → e.stacks i = a.stacks i) ∧
        (∀ i, (∀ j, p.register j ≠ i) → e.regs i = a.regs i) := by
  have hproject : projectState p.register p.stack a =
      SubexpAlphabetProgram.inputState (a.stacks (p.stack 0)) (a.regs ∘ p.register) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    by_cases hi : i = 0
    · subst i; rfl
    · simpa [projectState, SubexpAlphabetProgram.inputState, hi] using empty i hi
  obtain ⟨t, ht, b, hb, hout, hclean⟩ :=
    command_eval (a.stacks (p.stack 0)) (a.regs ∘ p.register)
  rw [← hproject] at hb
  let e := embedState p.register p.stack a b
  refine ⟨t+1, Nat.add_le_add_right ht 1, e,
    eval_liftCommand_from_state _ _ _ _ _ _ p.register_injective p.stack_injective hb,
    ?_, ?_, ?_, ?_⟩
  · exact (embedState_stack _ _ _ _ p.stack_injective 5).trans hout
  · intro i hi
    exact (embedState_stack _ _ _ _ p.stack_injective i).trans (hclean i hi)
  · intro i hi
    exact embedState_stack_frame _ _ _ _ i (by rintro ⟨j, hj⟩; exact hi j hj)
  · intro i hi
    exact embedState_register_frame _ _ _ _ i (by rintro ⟨j, hj⟩; exact hi j hj)

end SubexponentialSAT.SqrtLog.Execution.HashAlphabet

end OAI.Algorithms
