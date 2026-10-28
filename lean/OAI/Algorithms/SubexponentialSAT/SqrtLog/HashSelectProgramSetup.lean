import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramBounded
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramCost

namespace OAI.Algorithms

/-! A concrete 10-register, 14-stack layout joins runtime tuple generation to
the selector. It can be relocated into a larger evaluator with liftProgram. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp

private def coreRegister (i : Fin 8) : Fin 10 := ⟨i.val, by omega⟩
private def coreStack (i : Fin 9) : Fin 14 := ⟨i.val, by omega⟩

def localController : ControllerPorts 10 14 where
  trial := {
    core := {
      register := coreRegister
      stack := coreStack
      register_injective := by
        intro i j h
        apply Fin.ext
        exact congrArg (fun x : Fin 10 => x.val) h
      stack_injective := by
        intro i j h
        apply Fin.ext
        exact congrArg (fun x : Fin 14 => x.val) h }
    rows := 9
    family := 10
    rows_outside := by intro i h; have := congrArg Fin.val h; dsimp [coreStack] at this; omega
    family_outside := by intro i h; have := congrArg Fin.val h; dsimp [coreStack] at this; omega }
  loop := ⟨8, 9, 13, by decide⟩
  counter_outside := by intro i h; have := congrArg Fin.val h; dsimp [coreStack] at this; omega
  value_outside := by intro i h; have := congrArg Fin.val h; dsimp [coreRegister] at this; omega
  present_outside := by intro i h; have := congrArg Fin.val h; dsimp [coreRegister] at this; omega
  rows_ne_counter := by decide
  family_ne_counter := by decide
  family_ne_rows := by decide

abbrev localGenerate : GeneratePorts 10 14 where
  register := id
  stack := ![10, 11, 0, 1, 4, 5, 6, 7, 12]
  register_injective := Function.injective_id
  stack_injective := by decide

abbrev setup : Cmd 10 14 :=
  .seq (generate localGenerate) (.call (StackRoutines.clearProgram 5 0 1))

private theorem embed_projection {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (a : State R S) :
    embedState register stack a
      ⟨fun i => a.regs (register i), fun i => a.stacks (stack i)⟩ = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases hi : ∃ j, register j = i
    · obtain ⟨j, rfl⟩ := hi
      exact embedState_register register stack a _ hr j
    · exact embedState_register_frame register stack a _ i hi
  · funext i
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact embedState_stack register stack a _ hs j
    · exact embedState_stack_frame register stack a _ i hi

/-- Initial input convention: stacks 0..8 empty, rows in 9, family destination
10 empty, alphabet in 11, runtime tuple depth in 12, runtime K in 13. -/
theorem setup_eval (alphabet initial : Records) (depth : List Bool) (a : State 10 14)
    (he : ∀ i, a.stacks (localController.trial.core.stack i) = [])
    (hf : a.stacks 10 = [])
    (ha : a.stacks 11 = ProgramEncoding.encodeRecords alphabet)
    (hd : a.stacks 12 = depth)
    (hr : a.stacks 9 = candidateEncoding initial) :
    ∃ n ≤ TupleProgram.powerCost alphabet depth.length [[]] + 14,
      ∃ b : State 10 14,
        ControllerReady localController b (generatedPayloads alphabet depth.length) initial b ∧
        b.stacks 13 = a.stacks 13 ∧ b.stacks 11 = a.stacks 11 ∧ Eval setup n a b := by
  let d : State 10 9 := ⟨a.regs, fun i => a.stacks (localGenerate.stack i)⟩
  have hout : TupleProgram.outerInvariant alphabet depth (a.regs 9) d := by
    refine ⟨ha, he 1, he 4, he 6, he 7, hd, rfl⟩
  obtain ⟨n, hn, e, ready, hfamily, ht⟩ := generate_eval localGenerate a alphabet depth
    (a.regs 9) d hout hf (he 0) (he 5)
  have hstart : embedState localGenerate.register localGenerate.stack a d = a :=
    embed_projection _ _ localGenerate.register_injective localGenerate.stack_injective a
  rw [hstart] at ht
  let c := embedState localGenerate.register localGenerate.stack a e
  let b : State 10 14 := ⟨readRegs c.regs 0 1 none, StackRoutines.clearStacks 5 c.stacks⟩
  have hc : ∀ i, c.stacks (localGenerate.stack i) = e.stacks i :=
    embedState_stack _ _ _ _ localGenerate.stack_injective
  have outside : ∀ i, (∀ j, localGenerate.stack j ≠ i) → c.stacks i = a.stacks i := by
    intro i hi
    exact embedState_stack_frame _ _ _ _ i (by rintro ⟨j, hj⟩; exact hi j hj)
  have hc5 : c.stacks 5 = [false] := (hc 5).trans ready.2.2.2
  have hc2 : c.stacks 2 = [] := (outside 2 (by decide)).trans (he 2)
  have hc3 : c.stacks 3 = [] := (outside 3 (by decide)).trans (he 3)
  have hc8 : c.stacks 8 = [] := (outside 8 (by decide)).trans (he 8)
  have hc9 : c.stacks 9 = candidateEncoding initial := (outside 9 (by decide)).trans hr
  have hc13 : c.stacks 13 = a.stacks 13 := outside 13 (by decide)
  have hc11 : c.stacks 11 = a.stacks 11 := (hc 1).trans (ready.1.1.trans ha.symm)
  have hbc : ∀ i : Fin 14, b.stacks i = if i = 5 then [] else c.stacks i := by
    intro i; simp [b, StackRoutines.clearStacks, Function.update_apply]
  refine ⟨n + 5, by omega, b, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have h0 := (hc 2).trans ready.2.2.1
      have h1 := (hc 3).trans ready.1.2.1
      have h4 := (hc 4).trans ready.1.2.2.1
      have h6 := (hc 6).trans ready.1.2.2.2.1
      have h7 := (hc 7).trans ready.1.2.2.2.2.1
      fin_cases i
      · change b.stacks 0 = []; simpa [hbc] using h0
      · change b.stacks 1 = []; simpa [hbc] using h1
      · change b.stacks 2 = []; simpa [hbc] using hc2
      · change b.stacks 3 = []; simpa [hbc] using hc3
      · change b.stacks 4 = []; simpa [hbc] using h4
      · change b.stacks 5 = []; simp [hbc]
      · change b.stacks 6 = []; simpa [hbc] using h6
      · change b.stacks 7 = []; simpa [hbc] using h7
      · change b.stacks 8 = []; simpa [hbc] using hc8
    · exact (by simpa [localController, hbc, localGenerate] using (hc 0).trans hfamily)
    · simpa [localController, hbc] using hc9
    · intros; rfl
    · intros; rfl
  · simpa [hbc] using hc13
  · simpa [hbc] using hc11
  · have hclear := TupleProgram.clear_eval (5 : Fin 14) (0 : Fin 10) 1 c
    rw [hc5] at hclear
    exact Eval.seq ht hclear

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
