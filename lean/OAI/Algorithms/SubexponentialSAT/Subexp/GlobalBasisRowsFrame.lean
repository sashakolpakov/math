import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRows

namespace OAI.Algorithms

/-! Exact stack framing for the concrete dense-row traversal. -/

namespace SubexponentialSAT.Subexp.GlobalBasisRows

open BitProgram StructuredCalls
open GlobalBasisColumns (Descriptor)
open GlobalBasisEntry (Row Ready Valid)

theorem invariant_stack_frame {p : ℕ} [Fact p.Prime] {R : Row p} {a b : Data}
    (ha : Invariant R a) (hb : Invariant R b) (i : Fin 32)
    (h6 : i ≠ 6) (h7 : i ≠ 7) (h12 : i ≠ 12) : b.stacks i = a.stacks i := by
  rcases ha with ⟨ha, ha8, ha9, ha10⟩
  rcases hb with ⟨hb, hb8, hb9, hb10⟩
  by_cases hi : 16 ≤ i.val
  · rw [ha.work i hi, hb.work i hi]
  · have hlt : i.val < 16 := by omega
    interval_cases hv : i.val
    all_goals first
      | have hi : i = 0 := Fin.ext hv; subst i; exact hb.table.trans ha.table.symm
      | have hi : i = 1 := Fin.ext hv; subst i; exact hb.dimension.trans ha.dimension.symm
      | have hi : i = 2 := Fin.ext hv; subst i; exact hb.coordinate.trans ha.coordinate.symm
      | have hi : i = 3 := Fin.ext hv; subst i; exact hb.block.trans ha.block.symm
      | have hi : i = 4 := Fin.ext hv; subst i; exact hb.color.trans ha.color.symm
      | have hi : i = 5 := Fin.ext hv; subst i; exact hb.rank.trans ha.rank.symm
      | have hi : i = 6 := Fin.ext hv; exact (h6 hi).elim
      | have hi : i = 7 := Fin.ext hv; exact (h7 hi).elim
      | have hi : i = 8 := Fin.ext hv; subst i; exact hb8.trans ha8.symm
      | have hi : i = 9 := Fin.ext hv; subst i; exact hb9.trans ha9.symm
      | have hi : i = 10 := Fin.ext hv; subst i; exact hb10.trans ha10.symm
      | have hi : i = 11 := Fin.ext hv; subst i; exact hb.output.trans ha.output.symm
      | have hi : i = 12 := Fin.ext hv; exact (h12 hi).elim
      | have hi : i = 13 := Fin.ext hv; subst i; exact hb.width.trans ha.width.symm
      | have hi : i = 14 := Fin.ext hv; subst i; exact hb.zero.trans ha.zero.symm
      | have hi : i = 15 := Fin.ext hv; subst i; exact hb.one.trans ha.one.symm

/-- Arbitrary incoming control flags are accepted. The only changed stacks
are the consumed descriptor input and the reversed row accumulator. -/
theorem command_eval_from_state {p : ℕ} [Fact p.Prime] (R : Row p)
    (xs : List Descriptor) (suffix : List Bool) (d : Data)
    (hi : Invariant R d) (hv : ∀ x ∈ xs, Valid R x)
    (h6 : d.stacks 6 = Encoding.encodeList id (records xs) ++ suffix)
    (h7 : d.stacks 7 = []) :
    ∃ n e, n ≤ 3 + budget R xs ∧ Invariant R e ∧ Eval command n d e ∧
      e.stacks = Function.update (Function.update d.stacks 6 suffix) 12
        ((rowBits R xs).reverse ++ d.stacks 12) := by
  obtain ⟨n, e, hn, heI, he6, he7, he12, he⟩ :=
    command_eval R xs suffix d hi hv (d.regs 13) (d.regs 14) (d.regs 15)
  have hin : RecordPrograms.state ports d (d.regs 13) (d.regs 14) (d.regs 15)
      (Encoding.encodeList id (records xs) ++ suffix) [] = d :=
    RecordPrograms.state_eq_self ports d _ _ _ _ _ rfl rfl rfl h6 h7
  rw [hin] at he
  refine ⟨n, e, hn, heI, he, ?_⟩
  funext i
  by_cases hi6 : i = 6
  · subst i; simpa using he6
  by_cases hi7 : i = 7
  · subst i; simpa [h7] using he7
  by_cases hi12 : i = 12
  · subst i; simpa using he12
  simpa [hi6, hi12] using invariant_stack_frame hi heI i hi6 hi7 hi12

theorem program_runsIn_from_state {p : ℕ} [Fact p.Prime] (R : Row p)
    (xs : List Descriptor) (suffix : List Bool) (d : Data)
    (hi : Invariant R d) (hv : ∀ x ∈ xs, Valid R x)
    (h6 : d.stacks 6 = Encoding.encodeList id (records xs) ++ suffix)
    (h7 : d.stacks 7 = []) :
    ∃ e : Data, Invariant R e ∧
      RunsIn program (2000 * (baseSize R + encodedSize xs + 1)^4)
        (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update d.stacks 6 suffix) 12
        ((rowBits R xs).reverse ++ d.stacks 12) := by
  obtain ⟨n, e, hn, heI, he, hs⟩ := command_eval_from_state R xs suffix d hi hv h6 h7
  refine ⟨e, heI, ⟨n + 1, ?_, compiled_halt_trace he 6 12⟩, hs⟩
  exact (by omega : n + 1 ≤ 4 + budget R xs).trans (budget_polynomial R xs)

end SubexponentialSAT.Subexp.GlobalBasisRows

end OAI.Algorithms
