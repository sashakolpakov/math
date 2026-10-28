import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def Correct (d e : Data) : Prop :=
  SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 4) = incidence d ∧
  SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 5) = head d ∧
  (e.stacks 4).length ≤ 2 * (d.stacks 0).length + 2 * (d.stacks 1).length + 3 ∧
  (e.stacks 5).length ≤ 2 * (d.stacks 2).length + 2 * (d.stacks 3).length + 6 ∧
  (∀ j, j ≠ 4 → j ≠ 5 → e.stacks j = d.stacks j)

theorem program_runsIn (d : Data) (hd : ready d) :
    ∃ e : Data, RunsIn program (500 * (2 * inputLength d + 4)^2 + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧ Correct d e := by
  obtain ⟨t, ht, e, he, hc⟩ := command_eval d hd
  exact ⟨e, ⟨t+1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 4⟩, hc⟩

/-- One fixed finite primitive machine; the overhead depends only on its code. -/
theorem program_primitive (d : Data) (hd : ready d) :
    ∃ e : Data,
      SubexponentialSAT.Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (500 * (2 * inputLength d + 4)^2 + 1))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) ∧ Correct d e := by
  obtain ⟨e, he, hc⟩ := program_runsIn d hd
  exact ⟨e, primitive_execution program he, hc⟩

/-- Relocation preserves every unassigned register and every non-output stack,
including arbitrary caller data outside the local port block. -/
theorem command_lifted {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 13 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) (hd : ∀ j : Fin 13, 4 ≤ j.val → d.stacks (stack j) = []) :
    ∃ t ≤ 500 * (2 * inputLength (projectState register stack d) + 4)^2 + 1,
    ∃ e : State R S,
      Eval (liftCommand command 0 4 register stack) t d e ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks (stack 4)) =
        incidence (projectState register stack d) ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks (stack 5)) =
        head (projectState register stack d) ∧
      (e.stacks (stack 4)).length ≤
        2 * (d.stacks (stack 0)).length + 2 * (d.stacks (stack 1)).length + 3 ∧
      (e.stacks (stack 5)).length ≤
        2 * (d.stacks (stack 2)).length + 2 * (d.stacks (stack 3)).length + 6 ∧
      (∀ j, j ≠ stack 4 → j ≠ stack 5 → e.stacks j = d.stacks j) ∧
      (∀ j, (¬ ∃ i, register i = j) → e.regs j = d.regs j) := by
  let a := projectState register stack d
  obtain ⟨t, ht, b, he, hi, hh, hli, hlh, hf⟩ := command_eval a hd
  refine ⟨t+1, Nat.add_le_add_right ht 1, embedState register stack d b,
    eval_liftCommand_from_state command 0 4 register stack d hr hs he,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [embedState_stack register stack d b hs 4] using hi
  · simpa only [embedState_stack register stack d b hs 5] using hh
  · simpa [a, projectState, embedState_stack register stack d b hs 4] using hli
  · simpa [a, projectState, embedState_stack register stack d b hs 5] using hlh
  · intro j hj4 hj5
    by_cases hm : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hm
      rw [embedState_stack register stack d b hs i]
      exact hf i (fun h => hj4 (congrArg stack h)) (fun h => hj5 (congrArg stack h))
    · exact embedState_stack_frame register stack d b j hm
  · exact fun j hj => embedState_register_frame register stack d b j hj

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
