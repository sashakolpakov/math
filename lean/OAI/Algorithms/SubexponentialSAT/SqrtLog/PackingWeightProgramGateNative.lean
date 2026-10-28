import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgramGate

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The unary expansion is paid in the numeric value n, not only its bit size. -/
theorem budget_le (d : Data) : budget d ≤
    80 * (CounterPrograms.value (d.stacks 0) + (d.stacks 1).length + (d.stacks 0).length + 1)^2 := by
  unfold budget CounterConversions.runtimeBound
  nlinarith [Nat.zero_le (CounterPrograms.value (d.stacks 0) * (d.stacks 1).length),
    Nat.zero_le ((d.stacks 0).length * (d.stacks 1).length)]

theorem program_runsIn (d : Data) (hd : ready d) :
    ∃ e : Data, RunsIn program (budget d + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 2 = output d ∧ (∀ j, j ≠ 2 → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, e, he, ho, hf⟩ := command_eval d hd
  exact ⟨e, ⟨t+1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 2⟩, ho, hf⟩

theorem program_primitive (d : Data) (hd : ready d) :
    ∃ e : Data, SubexponentialSAT.Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (budget d + 1))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks 2 = output d ∧ (∀ j, j ≠ 2 → e.stacks j = d.stacks j) := by
  obtain ⟨e, he, ho, hf⟩ := program_runsIn d hd
  exact ⟨e, primitive_execution program he, ho, hf⟩

theorem command_lifted {R S : ℕ} (register : Fin 4 → Fin R) (stack : Fin 7 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) (hd : ∀ j : Fin 7, 2 ≤ j.val → d.stacks (stack j) = []) :
    ∃ t ≤ budget (projectState register stack d) + 1, ∃ e : State R S,
      Eval (liftCommand command 0 2 register stack) t d e ∧
      e.stacks (stack 2) = output (projectState register stack d) ∧
      (∀ j, j ≠ stack 2 → e.stacks j = d.stacks j) ∧
      (∀ j, (¬ ∃ i, register i = j) → e.regs j = d.regs j) := by
  obtain ⟨t, ht, b, he, ho, hf⟩ := command_eval (projectState register stack d) hd
  refine ⟨t+1, Nat.add_le_add_right ht 1, embedState register stack d b,
    eval_liftCommand_from_state command 0 2 register stack d hr hs he, ?_, ?_, ?_⟩
  · simpa only [embedState_stack register stack d b hs 2] using ho
  · intro j hj
    by_cases hm : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hm
      rw [embedState_stack register stack d b hs i]
      exact hf i (fun h => hj (congrArg stack h))
    · exact embedState_stack_frame register stack d b j hm
  · exact fun j hj => embedState_register_frame register stack d b j hj

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

end OAI.Algorithms
