import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHashInputs
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramSetupLift

namespace OAI.Algorithms

/-! Fixed native setup from three binary parameter words to the actual
candidate queue and runtime selector counter. The full caller frame remains
available to the eventual mass-evaluation callback. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashSetup

open BitProgram StructuredCalls HashSelectProgram
open SubexponentialSAT.Subexp

abbrev command : Cmd 10 14 := .seq HashInputs.command setup

def budget (count depth rounds : List Bool) : ℕ :=
  HashInputs.budget count depth rounds +
    TupleProgram.powerCost (SubexpAlphabetProgram.alphabetWords count)
      (CounterPrograms.value depth) [[]] + 14

theorem command_eval (initial : Records) (a : State 10 14)
    (ready : HashInputs.Ready a) (rows : a.stacks 9 = candidateEncoding initial) :
    ∃ t ≤ budget (a.stacks 0) (a.stacks 5) (a.stacks 6),
      ∃ b : State 10 14, Eval command t a b ∧
        ControllerReady localController b
          (generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 0))
            (CounterPrograms.value (a.stacks 5))) initial b ∧
        b.stacks 13 = List.replicate (CounterPrograms.value (a.stacks 6)) true := by
  obtain ⟨t1, ht1, b, hb, ha, hp, hk, hr, hf, he⟩ := HashInputs.command_eval a ready
  have hcore : ∀ i, b.stacks (localController.trial.core.stack i) = [] := he
  obtain ⟨t2, ht2, c, hc, hck, _, htrace⟩ := setup_eval
    (SubexpAlphabetProgram.alphabetWords (a.stacks 0)) initial
    (List.replicate (CounterPrograms.value (a.stacks 5)) true) b
    hcore hf ha hp (hr.trans rows)
  refine ⟨t1+t2, ?_, c, hb.seq htrace, ?_, hck.trans hk⟩
  · simp only [List.length_replicate] at ht2
    dsimp [budget]
    omega
  · simpa only [List.length_replicate] using hc

abbrev generate {R S : ℕ} (register : Fin 10 → Fin R) (stack : Fin 14 → Fin S) : Cmd R S :=
  liftCommand command 0 10 register stack

/-- The only inputs supplied to this setup are small binary parameter words
and the initial row stream. The alphabet and all candidate records are
actually generated. Arithmetic producing those binary parameters is charged
by its caller. -/
theorem generate_eval {R S : ℕ} (register : Fin 10 → Fin R) (stack : Fin 14 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (initial : Records) (a : State R S)
    (ready : HashInputs.Ready (projectState register stack a))
    (rows : a.stacks (stack 9) = candidateEncoding initial) :
    ∃ t ≤ budget (a.stacks (stack 0)) (a.stacks (stack 5)) (a.stacks (stack 6)) + 1,
      ∃ b : State R S, Eval (generate register stack) t a b ∧
        ControllerReady (relocateController register stack hregister hstack) b
          (generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks (stack 0)))
            (CounterPrograms.value (a.stacks (stack 5)))) initial b ∧
        b.stacks (stack 13) = List.replicate (CounterPrograms.value (a.stacks (stack 6))) true ∧
        (∀ i, (∀ j, stack j ≠ i) → b.stacks i = a.stacks i) ∧
        (∀ i, (∀ j, register j ≠ i) → b.regs i = a.regs i) := by
  obtain ⟨t, ht, c, hc, hready, hk⟩ :=
    command_eval initial (projectState register stack a) ready rows
  let b := embedState register stack a c
  have hs (i : Fin 14) : b.stacks (stack i) = c.stacks i :=
    embedState_stack register stack a c hstack i
  refine ⟨t+1, Nat.add_le_add_right ht 1, b,
    eval_liftCommand_from_state _ _ _ _ _ _ hregister hstack hc, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, (hs 10).trans hready.2.1, (hs 9).trans hready.2.2.1, ?_, ?_⟩
    · intro i
      exact (hs _).trans (hready.1 i)
    · intros; rfl
    · intros; rfl
  · exact (hs 13).trans hk
  · intro i hi
    exact embedState_stack_frame _ _ _ _ i (by rintro ⟨j, hj⟩; exact hi j hj)
  · intro i hi
    exact embedState_register_frame _ _ _ _ i (by rintro ⟨j, hj⟩; exact hi j hj)

end SubexponentialSAT.SqrtLog.Execution.HashSetup

end OAI.Algorithms
