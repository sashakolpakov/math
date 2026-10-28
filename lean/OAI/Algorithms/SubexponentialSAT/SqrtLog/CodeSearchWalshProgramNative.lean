import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem pass_iff (d : Data) : pass d = true ↔
    good (BinaryArithmetic.toNat (d.stacks 0)) (BinaryArithmetic.toNat (d.stacks 1)) (d.stacks 2).length := by
  simp [pass]

theorem program_runsIn (d : Data) (hd : ∀ j : Fin 14, 3 ≤ j.val → d.stacks j = []) :
    ∃ e : Data, RunsIn program (700 * (2 * size d + 4)^2 + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.regs 8 = pass d ∧ e.stacks = d.stacks := by
  obtain ⟨t, ht, e, he, ho, hf⟩ := command_eval d hd
  exact ⟨e, ⟨t+1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 0⟩, ho, hf⟩

theorem program_primitive (d : Data) (hd : ∀ j : Fin 14, 3 ≤ j.val → d.stacks j = []) :
    ∃ e : Data, SubexponentialSAT.Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (700 * (2 * size d + 4)^2 + 1))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.regs 8 = pass d ∧ e.stacks = d.stacks := by
  obtain ⟨e, he, ho, hf⟩ := program_runsIn d hd
  exact ⟨e, primitive_execution program he, ho, hf⟩

/-- The only retained result is the designated Boolean flag. Every caller stack
and every register outside the fixed local register image are preserved. -/
theorem command_lifted {R S : ℕ} (register : Fin 9 → Fin R) (stack : Fin 14 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) (hd : ∀ j : Fin 14, 3 ≤ j.val → d.stacks (stack j) = []) :
    ∃ t ≤ 700 * (2 * size (projectState register stack d) + 4)^2 + 1,
    ∃ e : State R S,
      Eval (liftCommand command 0 0 register stack) t d e ∧
      e.regs (register 8) = pass (projectState register stack d) ∧
      e.stacks = d.stacks ∧
      (∀ j, (¬ ∃ i, register i = j) → e.regs j = d.regs j) := by
  obtain ⟨t, ht, b, he, ho, hf⟩ := command_eval (projectState register stack d) hd
  refine ⟨t+1, Nat.add_le_add_right ht 1, embedState register stack d b,
    eval_liftCommand_from_state command 0 0 register stack d hr hs he, ?_, ?_, ?_⟩
  · simpa only [embedState_register register stack d b hr 8] using ho
  · funext j
    by_cases hm : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hm
      rw [embedState_stack register stack d b hs i, hf]
      rfl
    · exact embedState_stack_frame register stack d b j hm
  · exact fun j hj => embedState_register_frame register stack d b j hj

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
