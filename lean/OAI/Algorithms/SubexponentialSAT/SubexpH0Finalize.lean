import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpH0CountDecision
import OAI.Algorithms.SubexponentialSAT.SubexpMainReady

namespace OAI.Algorithms

/-! The singleton reconstruction output is decoded by the actual final phase,
including workspace cleanup and register reset before the next leaf. -/

namespace SubexponentialSAT.SubexpH0Finalize

open StructuredCalls SubexpMainProgram SubexpQuarticRing SubexpLayoutSpec

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p)) {c : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) S.toPattern c)

local notation "D" => Fintype.card V
local notation "B" => SubexpLiftRing.baseWidth p (D + 1)
local notation "coeffs" => QuarticSearch.liftedCoefficients p (D + 1)

omit [DecidableEq F] in
theorem execution {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (output : SubexpFlatCount.Code B) (hD : 0 < D)
    (computed : SubexpHornerMachine.decode p (D + 1) coeffs output =
      SubexpCRTAtZero.selectedValue S L)
    (a : MainState er es) (regs : Fin 8 → Bool) (width : List Bool)
    (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs M.bits width (SubexpFlatCount.flatPolynomial [output])) :
    ∃ (steps : ℕ) (rf : Fin 8 → Bool),
      steps ≤ 3 * SubexpH0CountDecision.budget B +
        2 * WorkspaceCleanupProgram.Main.selectedBits count hcount a +
        3 * count + workRegs er + 4 ∧
      Eval (SubexpMainReady.procedure er es count hcount).invoke steps a
        (SubexpMainReady.result count hcount a rf M.bits width output.c0.val) ∧
      SubexpMainReady.StorageReady count
        (SubexpMainReady.result count hcount a rf M.bits width output.c0.val) ∧
      (((SubexpMainReady.result count hcount a rf M.bits width output.c0.val).stacks
        (persistent es 10)).head? = some true ↔ ∃ x : V → ZMod p, Factor.Satisfies S x) ∧
      (∀ j : Fin 32, j ≠ 10 →
        (SubexpMainReady.result count hcount a rf M.bits width output.c0.val).stacks
          (persistent es j) = a.stacks (persistent es j)) := by
  have hB : 0 < B := by unfold SubexpLiftRing.baseWidth; positivity
  obtain ⟨steps, rf, hn, he, hs⟩ := SubexpMainReady.execution_selected
    count hcount hB [output] a regs M.bits width hwidth ready
  have hb := SubexpH0CountDecision.singleton_budget_le output M.bits M.length_le
  refine ⟨steps, rf, by omega, he, hs, ?_, ?_⟩
  · rw [SubexpMainReady.result_answer, Option.some.injEq]
    exact SubexpH0CountDecision.answer_iff S L M output hD computed
  · intro j hj
    by_cases h12 : j = 12
    · subst j
      exact (SubexpMainReady.result_modulus count hcount a rf M.bits width output.c0.val).trans
        (SubexpMainReady.input_modulus a regs M.bits width _ ready).symm
    by_cases h13 : j = 13
    · subst j
      exact (SubexpMainReady.result_width count hcount a rf M.bits width output.c0.val).trans
        (SubexpMainReady.input_width a regs M.bits width _ ready).symm
    exact SubexpMainReady.result_persistent_frame count hcount a rf M.bits width
      output.c0.val j hj h12 h13

omit [DecidableEq F] in
/-- The cost of clearing the workspace is charged to actual preceding
instructions, independently of how much unread leaf data remains stored. -/
theorem execution_after_prefix {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (output : SubexpFlatCount.Code B) (hD : 0 < D)
    (computed : SubexpHornerMachine.decode p (D + 1) coeffs output =
      SubexpCRTAtZero.selectedValue S L)
    (phase : MainCmd er es) (prefixSteps : ℕ) (start a : MainState er es)
    (storage : SubexpMainReady.StorageReady count start)
    (hprefix : Eval phase prefixSteps start a)
    (regs : Fin 8 → Bool) (width : List Bool) (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs M.bits width (SubexpFlatCount.flatPolynomial [output])) :
    ∃ (steps : ℕ) (rf : Fin 8 → Bool),
      steps ≤ 3 * (prefixSteps + SubexpH0CountDecision.budget B) +
        3 * count + workRegs er + 4 ∧
      Eval (.seq phase (SubexpMainReady.procedure er es count hcount).invoke) steps start
        (SubexpMainReady.result count hcount a rf M.bits width output.c0.val) ∧
      SubexpMainReady.StorageReady count
        (SubexpMainReady.result count hcount a rf M.bits width output.c0.val) ∧
      (((SubexpMainReady.result count hcount a rf M.bits width output.c0.val).stacks
        (persistent es 10)).head? = some true ↔ ∃ x : V → ZMod p, Factor.Satisfies S x) := by
  obtain ⟨n, rf, hn, he, hs, ha, _⟩ :=
    execution S L count hcount M output hD computed a regs width hwidth ready
  have hbits := SubexpMainReady.selectedBits_after_eval count hcount hprefix
  rw [SubexpMainReady.selectedBits_eq_zero count hcount start storage] at hbits
  exact ⟨prefixSteps + n, rf, by omega, .seq hprefix he, hs, ha⟩

end SubexponentialSAT.SubexpH0Finalize

end OAI.Algorithms
