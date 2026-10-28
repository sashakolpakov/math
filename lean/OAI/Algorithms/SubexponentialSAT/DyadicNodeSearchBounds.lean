import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFNodeSearchCosts
import OAI.Algorithms.SubexponentialSAT.DyadicWidthDriverBounds

namespace OAI.Algorithms

/-! Apply the dyadic numerical bounds to the actual setup-and-search run.
The count and index-width words are obtained from the executable setup. -/

namespace SubexponentialSAT.DyadicNodeSearchBounds

open BitProgram StructuredCalls ExecCNFNodeSearch
open ExecCNFWidthLoad (low)
open DyadicMaskedSearchBounds DyadicCallbackWordBounds DyadicNodeBudget

/-- Both fields refer to the stored threshold-bank words. -/
structure BankInputs (k T n : ℕ) (a : Data k) : Prop where
  value : ∀ d : ExecCNFWidthDriver.Width k,
    CounterPrograms.value (a.stacks (ExecCNFWidthLoad.bank k
      (ExecCNFWidthDriver.dimension d) (ExecCNFWidthDriver.dimension_le d))) =
      arity T n (ExecCNFWidthDriver.dimension d)
  length : ∀ d : ExecCNFWidthDriver.Width k,
    (a.stacks (ExecCNFWidthLoad.bank k (ExecCNFWidthDriver.dimension d)
      (ExecCNFWidthDriver.dimension_le d))).length ≤
      ArithmeticExpressionProgram.widthCoeff
        (SparsificationThresholdProgram.thresholdExpr (ExecCNFWidthDriver.dimension d)) *
          ((SparsificationBudgetProgram.outputWord T (SubexpPackingParameters.s n)).length + 1)

variable {k T n : ℕ} {F : Formula} {a : Data k}

theorem prepared_inputs (hb : BankInputs k T n a)
    (h14 : a.stacks (low k 14) = []) (h15 : a.stacks (low k 15) = [])
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hliteral : ∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1)
    (count width : List Bool) (hw : CounterPrograms.value width = DyadicWidth.width F.length)
    (hcl : count.length ≤ F.length) (hwl : width.length ≤ F.length + 1) :
    DyadicWidthDriverBounds.Inputs k T n F.length F count (prepared a count width) := by
  refine ⟨Nat.le_refl _, hwidth, hliteral, hcl.trans (Nat.le_succ _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prepared_width]; exact hw
  · rw [prepared_width]; exact hwl
  · exact (prepared_frame a count width (low k 14)
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans h14
  · exact (prepared_frame a count width (low k 15)
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans h15
  · intro d
    rw [prepared_frame a count width _
      (ExecCNFWidthLoad.bank_ne_low k _ _ 19) (ExecCNFWidthLoad.bank_ne_low k _ _ 20)]
    exact hb.value d
  · intro d
    rw [prepared_frame a count width _
      (ExecCNFWidthLoad.bank_ne_low k _ _ 19) (ExecCNFWidthLoad.bank_ne_low k _ _ 20)]
    exact hb.length d

/-- The returned instruction bound and the encoded-input allowance belong
to the same concrete setup-and-search execution. -/
theorem program_runs_costed (ha : Fresh F a) (hb : BankInputs k T n a)
    (h14 : a.stacks (low k 14) = []) (h15 : a.stacks (low k 15) = [])
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hliteral : ∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1) :
    ∃ (B : ℕ) (b : Data k),
      RunsIn (program k) B (a.withPC (some (program k).entry)) (b.withPC none) ∧
      (CandidatePrepareProgram.formulaCode F).length + B + 1 ≤
        budget k T (overheadCoefficient k T) n F.length := by
  obtain ⟨count, width, _, hw, hcl, hwl, ns, nt, visited, b,
    _, _, htrace, ht, _⟩ := ExecCNFNodeSearchCosts.program_runs k F a ha
  have hi := prepared_inputs hb h14 h15 hwidth hliteral count width hw hcl hwl
  have hbound := DyadicWidthDriverBounds.totalBound_with_setup_le hi
  refine ⟨ExecCNFNodeSearchCosts.bound k F a count width, b, ⟨ns + nt + 2, ht, htrace⟩, ?_⟩
  dsimp only [ExecCNFNodeSearchCosts.bound, setupBound]
  omega

open Filter SubexpPackingParameters

/-- Uniform over all actual node formulas and all threshold words emitted
within the proved arithmetic length bound. -/
theorem eventually_program_runs_squared_bound (k T : ℕ) :
    ∃ q : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (F : Formula) (a : Data k),
      F.length ≤ (2 * n + 1) ^ k → Fresh F a → BankInputs k T n a →
      a.stacks (low k 14) = [] → a.stacks (low k 15) = [] →
      (∀ C ∈ F, C.length ≤ k) →
      (∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1) →
      ∃ (B : ℕ) (b : Data k),
        RunsIn (program k) B (a.withPC (some (program k).entry)) (b.withPC none) ∧
        1001000 * ((CandidatePrepareProgram.formulaCode F).length + B + 1) ^ 2 ≤
          (n + 1) ^ ((s n + 2) ^ q) := by
  obtain ⟨q, hq⟩ := eventually_squared_budget_le_closed_power k T (overheadCoefficient k T)
  refine ⟨q, hq.mono ?_⟩
  intro n hn F a hm ha hb h14 h15 hw hl
  obtain ⟨B, b, hrun, hB⟩ := program_runs_costed ha hb h14 h15 hw hl
  exact ⟨B, b, hrun,
    (Nat.mul_le_mul_left 1001000 (Nat.pow_le_pow_left hB 2)).trans (hn F.length hm)⟩

theorem eventually_program_runs_subexponential (k T : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (F : Formula) (a : Data k),
      F.length ≤ (2 * n + 1) ^ k → Fresh F a → BankInputs k T n a →
      a.stacks (low k 14) = [] → a.stacks (low k 15) = [] →
      (∀ C ∈ F, C.length ≤ k) →
      (∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1) →
      ∃ (B : ℕ) (b : Data k),
        RunsIn (program k) B (a.withPC (some (program k).entry)) (b.withPC none) ∧
        ((1001000 * ((CandidatePrepareProgram.formulaCode F).length + B + 1) ^ 2 : ℕ) : ℝ) ≤
          (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [eventually_squared_budget_subexponential k T (overheadCoefficient k T)] with n hn
  intro F a hm ha hb h14 h15 hw hl
  obtain ⟨B, b, hrun, hB⟩ := program_runs_costed ha hb h14 h15 hw hl
  exact ⟨B, b, hrun,
    (Nat.cast_le.mpr (Nat.mul_le_mul_left 1001000 (Nat.pow_le_pow_left hB 2))).trans
      (hn F.length hm)⟩

end SubexponentialSAT.DyadicNodeSearchBounds

end OAI.Algorithms
