import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DyadicNodeSearchBounds
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyTraversalCost

namespace OAI.Algorithms

/-! The concrete observed splitter and its actual worklist update satisfy
one dyadic node bound. Persistent bank lengths are the only stored-word
size assumptions; the formula count and literal sizes are derived. -/

namespace SubexponentialSAT.DyadicSparsifyNodeBounds

open BitProgram StructuredCalls ExecSparsifyObserved ExecSparsifyEncoding
open ExecSparsifyNode (Data)
open ExecCNFWidthDriver (Width dimension dimension_le)
open DyadicMaskedSearchBounds DyadicNodeBudget

def BankLengths (k T n : ℕ) (frame : Data k) : Prop :=
  ∀ d : Width k,
    (frame.stacks (ExecSparsifyProgram.searchPort k
      (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d)))).length ≤
      ArithmeticExpressionProgram.widthCoeff
        (SparsificationThresholdProgram.thresholdExpr (dimension d)) *
          ((SparsificationBudgetProgram.outputWord T (SubexpPackingParameters.s n)).length + 1)

theorem arity_ge_two (k T n : ℕ) : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ arity T n j := by
  intro j hj _
  exact SparsificationConstants.threshold_ge_two (DyadicSchedule.M T n) j
    (DyadicSchedule.M_ge_two T n) hj

theorem localInput_bankWord {n k : ℕ} (frame : Data k) (F : Formula n) (d : Width k) :
    (localInput frame F).stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d)) =
      frame.stacks (ExecSparsifyProgram.searchPort k
        (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))) := by
  have hne : ExecSparsifyProgram.searchPort k
      (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d)) ≠ ExecSparsifyNode.port k 21 := by
    intro h
    have hv := congrArg Fin.val h
    change 5 + (33 + dimension d) = 21 at hv
    omega
  change (ExecSparsifyNode.headLoaded (encode F)
    (ExecSparsifyCanonicalHead.input encode frame F [] [] 0)).stacks _ = _
  rw [ExecSparsifyNode.headLoaded_stack_frame _ _ _ hne,
    ExecSparsifyCanonicalHead.input_search_stack]

theorem localInput_bankInputs {n k T : ℕ} (frame : Data k)
    (hb : BankValues (arity T n) frame) (hl : BankLengths k T n frame) (F : Formula n) :
    DyadicNodeSearchBounds.BankInputs k T n (localInput frame F) := by
  constructor
  · intro d
    rw [localInput_bankWord]
    simpa only [CounterPrograms.value_eq_toNat] using hb d
  · intro d
    rw [localInput_bankWord]
    exact hl d

theorem words_literal_length {n : ℕ} (F : Formula n) :
    ∀ C ∈ words F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1 := by
  exact DyadicCallbackInputs.encodedLiterals_bits F

/-- No abstract callback or search-time premise occurs in this node bound. -/
theorem node_work_le {n k T : ℕ} (frame : Data k)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues (arity T n) frame)
    (hl : BankLengths k T n frame) (F : Formula n) (hF : Ready k F) :
    ExecSparsifyExecution.cost frame (arity T n) hf hb (arity_ge_two k T n) F +
        ExecWorklistLoop.updateCost encode F
          (split frame (arity T n) hf hb (arity_ge_two k T n) F) + 3 ≤
      1001000 * (budget k T (overheadCoefficient k T) n F.length) ^ 2 := by
  obtain ⟨B, b, hr, hB⟩ := DyadicNodeSearchBounds.program_runs_costed
    (localInput_fresh frame hf F) (localInput_bankInputs frame hb hl F)
    (by simpa using ExecSparsifyExecution.localInput_low (F := F) hf 14)
    (by simpa using ExecSparsifyExecution.localInput_low (F := F) hf 15)
    (words_width F k hF.2.2) (words_literal_length F)
  have hwork := ExecSparsifyTraversalCost.node_work_le_body_of_runsIn frame (arity T n)
    hf hb (arity_ge_two k T n) F hF B b hr
  have hB' : (encode F).length + B + 1 ≤ budget k T (overheadCoefficient k T) n F.length := by
    simpa only [encode, words_length] using hB
  exact hwork.trans (Nat.mul_le_mul_left 1001000 (Nat.pow_le_pow_left hB' 2))

open Filter SubexpPackingParameters

/-- The exponent is fixed before the input size, the actual parameter
frame, and any normalized formula encountered in the worklist traversal. -/
theorem eventually_node_work_le_power (k T : ℕ) :
    ∃ q : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (frame : Data k)
      (hf : ExecSparsifyBoundary.FrameReady frame)
      (hb : BankValues (arity T n) frame),
      BankLengths k T n frame → ∀ F : Formula n, Ready k F →
      ExecSparsifyExecution.cost frame (arity T n) hf hb (arity_ge_two k T n) F +
          ExecWorklistLoop.updateCost encode F
            (split frame (arity T n) hf hb (arity_ge_two k T n) F) + 3 ≤
        (n + 1) ^ ((s n + 2) ^ q) := by
  obtain ⟨q, hq⟩ := eventually_squared_budget_le_closed_power k T (overheadCoefficient k T)
  refine ⟨q, hq.mono ?_⟩
  intro n hn frame hf hb hl F hF
  exact (node_work_le frame hf hb hl F hF).trans
    (hn F.length (ExecQuantitativeSparsify.raw_clause_count_le F k hF.1 hF.2.2))

theorem eventually_node_work_subexponential (k T : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (frame : Data k)
      (hf : ExecSparsifyBoundary.FrameReady frame)
      (hb : BankValues (arity T n) frame),
      BankLengths k T n frame → ∀ F : Formula n, Ready k F →
      ((ExecSparsifyExecution.cost frame (arity T n) hf hb (arity_ge_two k T n) F +
          ExecWorklistLoop.updateCost encode F
            (split frame (arity T n) hf hb (arity_ge_two k T n) F) + 3 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [eventually_squared_budget_subexponential k T (overheadCoefficient k T)] with n hn
  intro frame hf hb hl F hF
  exact (Nat.cast_le.mpr (node_work_le frame hf hb hl F hF)).trans
    (hn F.length (ExecQuantitativeSparsify.raw_clause_count_le F k hF.1 hF.2.2))

end SubexponentialSAT.DyadicSparsifyNodeBounds

end OAI.Algorithms
