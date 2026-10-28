import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramSetup

namespace OAI.Algorithms

/-! Only setup is lifted into the caller. The mass callback and selector are
compiled in the caller's full state space, so they can access its context. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp

variable {R S : ℕ}

def relocateController (register : Fin 10 → Fin R) (stack : Fin 14 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack) :
    ControllerPorts R S where
  trial := {
    core := {
      register := register ∘ localController.trial.core.register
      stack := stack ∘ localController.trial.core.stack
      register_injective := hregister.comp localController.trial.core.register_injective
      stack_injective := hstack.comp localController.trial.core.stack_injective }
    rows := stack 9
    family := stack 10
    rows_outside := fun i h => localController.trial.rows_outside i (hstack h)
    family_outside := fun i h => localController.trial.family_outside i (hstack h) }
  loop := ⟨register 8, register 9, stack 13, fun h => localController.loop.value_ne_present (hregister h)⟩
  counter_outside := fun i h => localController.counter_outside i (hstack h)
  value_outside := fun i h => localController.value_outside i (hregister h)
  present_outside := fun i h => localController.present_outside i (hregister h)
  rows_ne_counter := fun h => localController.rows_ne_counter (hstack h)
  family_ne_counter := fun h => localController.family_ne_counter (hstack h)
  family_ne_rows := fun h => localController.family_ne_rows (hstack h)

def setupProgram := compiled setup 12 10

abbrev setupLifted (register : Fin 10 → Fin R) (stack : Fin 14 → Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram setupProgram register stack)

private theorem project_embedding (register : Fin 10 → Fin R) (stack : Fin 14 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (a : State R S) :
    embedState register stack a ⟨a.regs ∘ register, a.stacks ∘ stack⟩ = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases hi : ∃ j, register j = i
    · obtain ⟨j, rfl⟩ := hi
      exact embedState_register register stack a _ hregister j
    · exact embedState_register_frame register stack a _ i hi
  · funext i
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact embedState_stack register stack a _ hstack j
    · exact embedState_stack_frame register stack a _ i hi

/-- Mapped setup leaves all formula/ring context outside its ports unchanged.
The subsequent callback is a command on the full caller state space. -/
theorem setup_eval_lifted (register : Fin 10 → Fin R) (stack : Fin 14 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (alphabet initial : Records) (depth : List Bool) (a : State R S)
    (he : ∀ i, a.stacks (stack (localController.trial.core.stack i)) = [])
    (hf : a.stacks (stack 10) = [])
    (ha : a.stacks (stack 11) = ProgramEncoding.encodeRecords alphabet)
    (hd : a.stacks (stack 12) = depth)
    (hr : a.stacks (stack 9) = candidateEncoding initial) :
    ∃ n ≤ TupleProgram.powerCost alphabet depth.length [[]] + 15, ∃ b : State R S,
      ControllerReady (relocateController register stack hregister hstack) b
        (generatedPayloads alphabet depth.length) initial b ∧
      b.stacks (stack 13) = a.stacks (stack 13) ∧
      b.stacks (stack 11) = a.stacks (stack 11) ∧
      (∀ i, (∀ j, stack j ≠ i) → b.stacks i = a.stacks i) ∧
      (∀ i, (∀ j, register j ≠ i) → b.regs i = a.regs i) ∧
      Eval (setupLifted register stack) n a b := by
  let projected : State 10 14 := ⟨a.regs ∘ register, a.stacks ∘ stack⟩
  obtain ⟨n, hn, b, hb, hc, halphabet, ht⟩ := setup_eval alphabet initial depth projected he hf ha hd hr
  let result := embedState register stack a b
  have hs : ∀ i, result.stacks (stack i) = b.stacks i :=
    embedState_stack register stack a b hstack
  have htrace := eval_call_lifted setupProgram register stack a hregister hstack
    (compiled_halt_trace ht 12 10)
  dsimp only [projected] at htrace
  rw [project_embedding register stack hregister hstack a] at htrace
  refine ⟨n + 1, by omega, result, ?_, ?_, ?_, ?_, ?_, htrace⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (hs _).trans (hb.1 i)
    · exact (hs 10).trans hb.2.1
    · exact (hs 9).trans hb.2.2.1
    · intros; rfl
    · intros; rfl
  · exact (hs 13).trans hc
  · exact (hs 11).trans halphabet
  · intro i hi
    exact embedState_stack_frame _ _ _ _ i (by rintro ⟨j, hj⟩; exact hi j hj)
  · intro i hi
    exact embedState_register_frame register stack a b i (by rintro ⟨j, hj⟩; exact hi j hj)

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
