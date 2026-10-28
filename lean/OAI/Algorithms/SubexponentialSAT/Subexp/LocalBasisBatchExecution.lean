import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchColor

namespace OAI.Algorithms

/-! Complete fixed execution of all local basis searches in position/color order. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls

theorem widthResult_boundary (ctx : Context) (r Q : ℕ) (regs : Fin 32 → Bool) :
    widthResult r Q (inputState ctx regs) =
      boundaryState ctx (TypeIndexProgram.unary (Q * r)) 0 0 [] [] [] []
        (widthResult r Q (inputState ctx regs)).regs := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    by_cases h117 : j = 117
    · subst j; rfl
    by_cases h118 : j = 118
    · subst j; rfl
    by_cases h119 : j = 119
    · subst j; rfl
    by_cases h120 : j = 120
    · subst j; rfl
    by_cases h121 : j = 121
    · subst j; rfl
    by_cases h122 : j = 122
    · subst j; rfl
    by_cases h127 : j = 127
    · subst j; rfl
    simp [widthResult, outputState, h117, h118, h119, h120,
      h121, h122, h127]
    rfl

noncomputable def sourceBudget (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (coefficients alphabet : List (ZMod p)) : ℕ :=
  widthCost r Q + coreCost r Q (colorBudget (Δ := Δ) p hr hQ coefficients alphabet) + 1

/-- No matrix, dimension word, prepared read plan, or callback execution
is assumed. Each result record carries the successful table actually found
by the fixed search in the order of the physical Side/Joint enumeration. -/
theorem program_runsIn (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (h2 : (2 : ZMod p) ≠ 0) (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet)
    (regs : Fin 32 → Bool) :
    ∃ rows finalRegs,
      RowsGood (GoodResult (Δ := Δ) p hr hQ coefficients) r Q rows ∧
      RunsIn program (sourceBudget (Δ := Δ) p hr hQ coefficients alphabet)
        ((inputState (canonicalContext p r Q Δ coefficients alphabet) regs).withPC
          (some program.entry))
        ((outputState (canonicalContext p r Q Δ coefficients alphabet)
          (TypeIndexProgram.unary (Q * r))
          (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords)) finalRegs).withPC none) := by
  let ctx := canonicalContext p r Q Δ coefficients alphabet
  let a := inputState ctx regs
  let b := widthResult r Q a
  have hw := makeWidth_eval r Q a (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have hb := widthResult_boundary ctx r Q regs
  obtain ⟨n, rows, finalRegs, hn, hg, he⟩ := batchCore_eval colorBody ctx
    (TypeIndexProgram.unary (Q * r)) r Q
    (colorBudget (Δ := Δ) p hr hQ coefficients alphabet)
    (GoodResult (Δ := Δ) p hr hQ coefficients)
    (actualColorStep p h2 hr hQ coefficients alphabet hfull)
    (canonicalContext_lengths p r Q Δ coefficients alphabet).1
    (canonicalContext_lengths p r Q Δ coefficients alphabet).2.1 b.regs
  rw [← hb] at he
  have hall : Eval command (widthCost r Q + n) a
      (outputState ctx (TypeIndexProgram.unary (Q * r))
        (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords)) finalRegs) :=
    hw.seq he
  refine ⟨rows, finalRegs, hg, widthCost r Q + n + 1, ?_, compiled_halt_trace hall 107 127⟩
  exact Nat.add_le_add_right (Nat.add_le_add_left hn (widthCost r Q)) 1

theorem primitive_runsIn (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (h2 : (2 : ZMod p) ≠ 0) (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet)
    (regs : Fin 32 → Bool) :
    ∃ rows finalRegs,
      RowsGood (GoodResult (Δ := Δ) p hr hQ coefficients) r Q rows ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * sourceBudget (Δ := Δ) p hr hQ coefficients alphabet)
        (primitiveCfg program ((inputState (canonicalContext p r Q Δ coefficients alphabet) regs).withPC
          (some program.entry)))
        (primitiveCfg program ((outputState (canonicalContext p r Q Δ coefficients alphabet)
          (TypeIndexProgram.unary (Q * r))
          (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords)) finalRegs).withPC none)) := by
  obtain ⟨rows, finalRegs, hg, he⟩ := program_runsIn p h2 hr hQ coefficients alphabet hfull regs
  exact ⟨rows, finalRegs, hg, primitive_execution program he⟩

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
