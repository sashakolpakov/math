import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyExecution

namespace OAI.Algorithms

/-!
# Local cost of observed splitting and the actual worklist update

The child words are bounded using the proved output-size theorems for the
two concrete child programs.  Their size is therefore not an extra premise
of the traversal bound.  Only the isolated local search input and its actual
instruction count occur in the final bound; pending and leaf tails do not.
-/

namespace SubexponentialSAT.ExecSparsifyTraversalCost

open BitProgram StructuredCalls
open ExecSparsifyObserved ExecSparsifyEncoding ExecSparsifySearchWitness
open ExecCNFWidthLoad (low)

variable {n k : ℕ} {frame : ExecSparsifyNode.Data k} {z : ℕ → ℕ} {F : Formula n}

/-- Both concrete child words fit inside the already charged branch volume. -/
theorem children_length_le_volume {b : ExecCNFNodeSearch.Data k}
    (w : TypedWitness F z b) :
    (encode (children w).1).length ≤
        ExecBranchController.volume (codes F) (codes w.selected)
          (w.core.map Encoding.literalCode) ∧
      (encode (children w).2).length ≤
        ExecBranchController.volume (codes F) (codes w.selected)
          (w.core.map Encoding.literalCode) := by
  have ha := ExecCoreChildProgram.result_length_le (codes F) (codes w.selected)
    (w.core.map Encoding.literalCode)
  have hb := ExecPetalChildProgram.result_length_le (codes F) (codes w.selected)
    (w.core.map Encoding.literalCode)
  have hva : (ExecCoreChildProgram.formulaCode (codes F)).length +
      2 * (ExecCoreChildProgram.clauseCode (w.core.map Encoding.literalCode)).length + 2 ≤
      ExecBranchController.volume (codes F) (codes w.selected)
        (w.core.map Encoding.literalCode) := by
    unfold ExecBranchController.volume ExecCoreChildProgram.inputVolume
    omega
  constructor
  · change (encode (ExecCoreChildProgram.result F w.selected w.core)).length ≤ _
    rw [encode_eq, ← ExecSparsifyChildSemantics.core_codes]
    exact ha.trans hva
  · change (encode (ExecPetalChildProgram.result F w.selected w.core)).length ≤ _
    rw [encode_eq, ← ExecSparsifyChildSemantics.petal_codes]
    exact (Nat.le_add_right _ 1).trans hb

/-- The search has physically retained the parent, core, and selected words. -/
theorem children_length_le (e : Execution frame z F)
    (hn : e.final.stacks (low k 21) ≠ []) :
    (encode (children (witness e hn)).1).length ≤ 4 * stackBits e.final.stacks + 3 ∧
      (encode (children (witness e hn)).2).length ≤ 4 * stackBits e.final.stacks + 3 := by
  have h := children_length_le_volume (witness e hn)
  have hv := ExecSparsifyExecution.child_volume_le e hn
  exact ⟨h.1.trans hv, h.2.trans hv⟩

/-- The exact updater cost is linear in the final local search store. -/
theorem updateCost_le_final (e : Execution frame z F) :
    ExecWorklistLoop.updateCost encode F (splitAt e) ≤
      109 * stackBits e.final.stacks + 124 := by
  classical
  have hF := ExecSparsifyExecution.word_length_le e (low k 16)
  rw [e.source, ← encode_eq] at hF
  by_cases hn : e.final.stacks (low k 21) = []
  · rw [splitAt, dite_eq_left hn]
    change 13 * (encode F).length + 20 ≤ _
    omega
  · have hc := children_length_le e hn
    rw [splitAt, dite_eq_right hn]
    change 5 * (encode F).length +
      13 * (encode (children (witness e hn)).2).length +
      13 * (encode (children (witness e hn)).1).length + 46 ≤ _
    omega

/-- Each real search instruction allocates at most one bit. -/
theorem updateCost_le (e : Execution frame z F) :
    ExecWorklistLoop.updateCost encode F (splitAt e) ≤
      124 * (stackBits (localInput frame F).stacks + e.steps + 1) ^ 2 := by
  have hs := trace_dataBits (ExecCNFNodeSearch.program k) e.trace
  change stackBits e.final.stacks ≤ stackBits (localInput frame F).stacks + e.steps at hs
  have hu := updateCost_le_final e
  have hl : ExecWorklistLoop.updateCost encode F (splitAt e) ≤
      109 * (stackBits (localInput frame F).stacks + e.steps) + 124 := by
    omega
  exact hl.trans (by nlinarith)

/-- Includes the three actual loop-control instructions charged per node. -/
theorem execution_work_le (e : Execution frame z F) :
    ExecSparsifyExecution.executionCost e +
        ExecWorklistLoop.updateCost encode F (splitAt e) + 3 ≤
      1001000 * (stackBits (localInput frame F).stacks + e.steps + 1) ^ 2 := by
  have hs := ExecSparsifyExecution.executionCost_le e
  have hu := updateCost_le e
  have hp : 1 ≤ (stackBits (localInput frame F).stacks + e.steps + 1) ^ 2 := by
    have hpos : 0 < stackBits (localInput frame F).stacks + e.steps + 1 := by omega
    exact Nat.succ_le_of_lt (pow_pos hpos 2)
  omega

theorem execution_cost_le (e : Execution frame z F) :
    ExecSparsifyExecution.executionCost e +
        ExecWorklistLoop.updateCost encode F (splitAt e) ≤
      1001000 * (stackBits (localInput frame F).stacks + e.steps + 1) ^ 2 := by
  have h := execution_work_le e
  omega

/-- The concrete observed split and concrete updater have one local bound. -/
theorem node_work_le (frame : ExecSparsifyNode.Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F) :
    ExecSparsifyExecution.cost frame z hf hb hz F +
        ExecWorklistLoop.updateCost encode F (split frame z hf hb hz F) + 3 ≤
      1001000 * (stackBits (localInput frame F).stacks +
        (observe frame z hf hb hz F hF).steps + 1) ^ 2 := by
  classical
  simpa only [ExecSparsifyExecution.cost, split, dite_eq_left hF] using
    execution_work_le (observe frame z hf hb hz F hF)

theorem node_cost_le (frame : ExecSparsifyNode.Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F) :
    ExecSparsifyExecution.cost frame z hf hb hz F +
        ExecWorklistLoop.updateCost encode F (split frame z hf hb hz F) ≤
      1001000 * (stackBits (localInput frame F).stacks +
        (observe frame z hf hb hz F hF).steps + 1) ^ 2 := by
  have h := node_work_le frame z hf hb hz F hF
  omega

/-- A concrete bounded search run supplies the numeric bound for this same
observed branch; deterministic trace uniqueness is proved in Execution. -/
theorem node_work_le_of_runsIn (frame : ExecSparsifyNode.Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F)
    (bound : ℕ) (b : ExecCNFNodeSearch.Data k)
    (hrun : RunsIn (ExecCNFNodeSearch.program k) bound
      ((localInput frame F).withPC (some (ExecCNFNodeSearch.program k).entry))
      (b.withPC none)) :
    ExecSparsifyExecution.cost frame z hf hb hz F +
        ExecWorklistLoop.updateCost encode F (split frame z hf hb hz F) + 3 ≤
      1001000 * (stackBits (localInput frame F).stacks + bound + 1) ^ 2 := by
  apply (node_work_le frame z hf hb hz F hF).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have ht := ExecSparsifyExecution.observed_steps_le
    (observe frame z hf hb hz F hF) bound b hrun
  omega

theorem node_cost_le_of_runsIn (frame : ExecSparsifyNode.Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F)
    (bound : ℕ) (b : ExecCNFNodeSearch.Data k)
    (hrun : RunsIn (ExecCNFNodeSearch.program k) bound
      ((localInput frame F).withPC (some (ExecCNFNodeSearch.program k).entry))
      (b.withPC none)) :
    ExecSparsifyExecution.cost frame z hf hb hz F +
        ExecWorklistLoop.updateCost encode F (split frame z hf hb hz F) ≤
      1001000 * (stackBits (localInput frame F).stacks + bound + 1) ^ 2 := by
  have h := node_work_le_of_runsIn frame z hf hb hz F hF bound b hrun
  omega

/-- The same child estimate uses only the active low32 search stacks. -/
theorem children_length_le_local (e : Execution frame z F)
    (hn : e.final.stacks (low k 21) ≠ []) :
    (encode (children (witness e hn)).1).length ≤
        4 * ExecSparsifySearchFrame.localSearchBits e.final + 3 ∧
      (encode (children (witness e hn)).2).length ≤
        4 * ExecSparsifySearchFrame.localSearchBits e.final + 3 := by
  have h := children_length_le_volume (witness e hn)
  have hv := ExecSparsifyExecution.child_volume_le_local e hn
  exact ⟨h.1.trans hv, h.2.trans hv⟩

theorem updateCost_le_final_local (e : Execution frame z F) :
    ExecWorklistLoop.updateCost encode F (splitAt e) ≤
      109 * ExecSparsifySearchFrame.localSearchBits e.final + 124 := by
  classical
  have hF := ExecSparsifySearchFrame.low_word_length_le e.final (16 : Fin 32)
  rw [e.source, ← encode_eq] at hF
  by_cases hn : e.final.stacks (low k 21) = []
  · rw [splitAt, dite_eq_left hn]
    change 13 * (encode F).length + 20 ≤ _
    omega
  · have hc := children_length_le_local e hn
    rw [splitAt, dite_eq_right hn]
    change 5 * (encode F).length +
      13 * (encode (children (witness e hn)).2).length +
      13 * (encode (children (witness e hn)).1).length + 46 ≤ _
    omega

/-- Cache words and parameter words outside the active block do not enter. -/
theorem updateCost_le_body (e : Execution frame z F)
    (hf : ExecSparsifyBoundary.FrameReady frame) :
    ExecWorklistLoop.updateCost encode F (splitAt e) ≤
      124 * ((encode F).length + e.steps + 1) ^ 2 := by
  have hs := ExecSparsifySearchFrame.localSearchBits_trace_le
    (localInput frame F) e.final e.trace
  rw [ExecSparsifyExecution.localInput_bits hf] at hs
  have hu := updateCost_le_final_local e
  have hl : ExecWorklistLoop.updateCost encode F (splitAt e) ≤
      109 * ((encode F).length + e.steps) + 124 := by
    omega
  exact hl.trans (by nlinarith)

theorem execution_work_le_body (e : Execution frame z F)
    (hf : ExecSparsifyBoundary.FrameReady frame) :
    ExecSparsifyExecution.executionCost e +
        ExecWorklistLoop.updateCost encode F (splitAt e) + 3 ≤
      1001000 * ((encode F).length + e.steps + 1) ^ 2 := by
  have hs := ExecSparsifyExecution.executionCost_le_body e hf
  have hu := updateCost_le_body e hf
  have hp : 1 ≤ ((encode F).length + e.steps + 1) ^ 2 := by
    have hpos : 0 < (encode F).length + e.steps + 1 := by omega
    exact Nat.succ_le_of_lt (pow_pos hpos 2)
  omega

/-- A node's local work depends on its own formula and search time, with
arbitrary preserved caller caches and worklist tails. -/
theorem node_work_le_body (frame : ExecSparsifyNode.Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F) :
    ExecSparsifyExecution.cost frame z hf hb hz F +
        ExecWorklistLoop.updateCost encode F (split frame z hf hb hz F) + 3 ≤
      1001000 * ((encode F).length + (observe frame z hf hb hz F hF).steps + 1) ^ 2 := by
  classical
  simpa only [ExecSparsifyExecution.cost, split, dite_eq_left hF] using
    execution_work_le_body (observe frame z hf hb hz F hF) hf

theorem node_cost_le_body (frame : ExecSparsifyNode.Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F) :
    ExecSparsifyExecution.cost frame z hf hb hz F +
        ExecWorklistLoop.updateCost encode F (split frame z hf hb hz F) ≤
      1001000 * ((encode F).length + (observe frame z hf hb hz F hF).steps + 1) ^ 2 := by
  have h := node_work_le_body frame z hf hb hz F hF
  omega

theorem node_work_le_body_of_runsIn (frame : ExecSparsifyNode.Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F)
    (bound : ℕ) (b : ExecCNFNodeSearch.Data k)
    (hrun : RunsIn (ExecCNFNodeSearch.program k) bound
      ((localInput frame F).withPC (some (ExecCNFNodeSearch.program k).entry))
      (b.withPC none)) :
    ExecSparsifyExecution.cost frame z hf hb hz F +
        ExecWorklistLoop.updateCost encode F (split frame z hf hb hz F) + 3 ≤
      1001000 * ((encode F).length + bound + 1) ^ 2 := by
  apply (node_work_le_body frame z hf hb hz F hF).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have ht := ExecSparsifyExecution.observed_steps_le
    (observe frame z hf hb hz F hF) bound b hrun
  omega

theorem node_cost_le_body_of_runsIn (frame : ExecSparsifyNode.Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F)
    (bound : ℕ) (b : ExecCNFNodeSearch.Data k)
    (hrun : RunsIn (ExecCNFNodeSearch.program k) bound
      ((localInput frame F).withPC (some (ExecCNFNodeSearch.program k).entry))
      (b.withPC none)) :
    ExecSparsifyExecution.cost frame z hf hb hz F +
        ExecWorklistLoop.updateCost encode F (split frame z hf hb hz F) ≤
      1001000 * ((encode F).length + bound + 1) ^ 2 := by
  have h := node_work_le_body_of_runsIn frame z hf hb hz F hF bound b hrun
  omega

end SubexponentialSAT.ExecSparsifyTraversalCost

end OAI.Algorithms
