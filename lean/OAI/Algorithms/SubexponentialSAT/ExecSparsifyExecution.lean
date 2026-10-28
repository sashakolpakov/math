import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyObserved
import OAI.Algorithms.SubexponentialSAT.ExecSparsifySearchFrame
import OAI.Algorithms.SubexponentialSAT.ExecWorklistLoopBounded
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace

namespace OAI.Algorithms

/-!
# The fixed node program realizes its observed sunflower branch

A canonical local search trace is lifted unchanged over arbitrary pending and
leaf streams.  The real child programs and return paths restore the exact
outer worklist frame.  The local cost uses only the bounded head and the local
search configuration, never either accumulated stream.
-/

namespace SubexponentialSAT.ExecSparsifyExecution

open BitProgram StructuredCalls ExecCNF
open ExecSparsifyNode ExecSparsifyObserved ExecSparsifyEncoding
open ExecSparsifyCanonicalHead ExecSparsifyBoundary ExecSparsifySearchFrame
open ExecSparsifySearchWitness (natClauseCode natFormulaCode)
open ExecCNFWidthLoad (low)

variable {n k : ℕ} {frame : Data k} {z : ℕ → ℕ} {F : Formula n}

noncomputable def after (e : Execution frame z F) (pending leaves : List (Formula n)) : Data k :=
  searched (encode F) (input encode frame F pending leaves 0) e.final

theorem local_frame (e : Execution frame z F) (pending leaves : List (Formula n)) :
    ExecCNFNodeSearch.Frame k
      (projectState id (ExecSparsifyProgram.searchPort k)
        (headLoaded (encode F) (input encode frame F pending leaves 0))) e.final := by
  rw [projected_head_eq]
  exact e.frame_preserved

theorem after_core (e : Execution frame z F) (pending leaves : List (Formula n))
    (i : Fin (k + 39)) (hi : i.val < 5) :
    (after e pending leaves).stacks i = (input encode frame F pending leaves 0).stacks i :=
  searched_core_frame (encode F) _ e.final i hi

theorem after_parameter (e : Execution frame z F) (pending leaves : List (Formula n))
    (i : Fin (k + 39)) (hi : 37 ≤ i.val) :
    (after e pending leaves).stacks i = frame.stacks i :=
  (searched_parameter_frame (encode F) _ e.final (local_frame e pending leaves) i hi).trans
    (input_stack_frame encode frame F pending leaves 0 i (by omega))

theorem after_empty (e : Execution frame z F) (hf : FrameReady frame)
    (pending leaves : List (Formula n)) (i : Fin (k + 39))
    (hi : 2 ≤ i.val ∧ i.val ≤ 7) : (after e pending leaves).stacks i = [] := by
  have hc := input_clean encode frame hf F pending leaves 0
  by_cases h5 : i.val < 5
  · rw [after_core e pending leaves i h5]
    exact hc i hi.1 (by omega)
  · exact searched_work_empty (encode F) _ e.final hc (local_frame e pending leaves) i (by omega)

theorem after_stack (e : Execution frame z F) (pending leaves : List (Formula n))
    (i : Fin (k + 34)) :
    (after e pending leaves).stacks (ExecSparsifyProgram.searchPort k i) = e.final.stacks i :=
  searched_stack (encode F) _ e.final i

/-- Exactly the same finite search trace runs over every pair of tails. -/
theorem start_eval (e : Execution frame z F) (hf : FrameReady frame)
    (pending leaves : List (Formula n)) :
    Eval (ExecSparsifyProgram.start k) (24 * (encode F).length + 29 + e.steps)
      (input encode frame F pending leaves 0) (after e pending leaves) := by
  have hc := input_clean encode frame hf F pending leaves 0
  have hh := readHead_eval (input encode frame F pending leaves 0) (encode F)
    (Encoding.encodeList encode pending)
    (by rw [input_pending]; rfl)
    (hc (port k 21) (by change 2 ≤ (21 : ℕ); omega) (by change (21 : ℕ) < 37; omega))
    (hc (port k 5) (by change 2 ≤ (5 : ℕ); omega) (by change (5 : ℕ) < 37; omega))
    (hc (port k 6) (by change 2 ≤ (6 : ℕ); omega) (by change (6 : ℕ) < 37; omega))
  have ht : Trace (ExecCNFNodeSearch.program k) e.steps
      ((projectState id (ExecSparsifyProgram.searchPort k)
        (headLoaded (encode F) (input encode frame F pending leaves 0))).withPC
          (some (ExecCNFNodeSearch.program k).entry)) (e.final.withPC none) := by
    rw [projected_head_eq]
    exact e.trace
  have hs := eval_call_from_state (ExecCNFNodeSearch.program k) id
    (ExecSparsifyProgram.searchPort k)
    (headLoaded (encode F) (input encode frame F pending leaves 0))
    Function.injective_id (ExecSparsifyProgram.searchPort_injective k) ht
  exact hh.seq hs

theorem terminal_output (e : Execution frame z F) (hf : FrameReady frame)
    (pending leaves : List (Formula n)) :
    terminalReturned (after e pending leaves) =
      ExecWorklistLoop.Ambient.liftData coreReg (coreStack k) frame
        (ExecWorklistLoop.splitData encode F pending leaves none) := by
  apply output_eq encode frame _ F pending leaves none hf
  · intro i
    simp [terminalReturned, Function.update_apply]
  · intro i
    have hi : (coreStack k i).val < 5 := i.isLt
    rw [terminalReturned_frame _ _ (Or.inl hi), after_core e pending leaves _ hi,
      input_core]
  · intro i hi hj
    exact terminalReturned_clean _ i ⟨hi, hj⟩
  · intro i hi
    rw [terminalReturned_frame _ _ (Or.inr hi)]
    exact after_parameter e pending leaves i hi

theorem branch_output (e : Execution frame z F) (hf : FrameReady frame)
    (pending leaves : List (Formula n)) (hn : e.final.stacks (low k 21) ≠ []) :
    branchProduced (ExecSparsifyProgram.peeked (after e pending leaves))
        (codes F) (codes (witness e hn).selected) ((witness e hn).core.map Encoding.literalCode) =
      ExecWorklistLoop.Ambient.liftData coreReg (coreStack k) frame
        (ExecWorklistLoop.splitData encode F pending leaves (some (children (witness e hn)))) := by
  let w := witness e hn
  let q := after e pending leaves
  apply output_eq encode frame _ F pending leaves (some (children w)) hf
  · intro i
    simp only [branchProduced_register, Option.isNone_some, ite_self]
  · intro i
    fin_cases i
    · change (branchProduced _ _ _ _).stacks (port k 0) = _
      rw [branchProduced_pending]
      change q.stacks (port k 0) = _
      rw [after_core e pending leaves (port k 0) (by change (0 : ℕ) < 5; omega), input_pending]
      rfl
    · change (branchProduced _ _ _ _).stacks (port k 1) = _
      rw [branchProduced_leaves]
      change q.stacks (port k 1) = _
      rw [after_core e pending leaves (port k 1) (by change (1 : ℕ) < 5; omega), input_leaves]
      rfl
    · change (branchProduced _ _ _ _).stacks (port k 2) = _
      rw [branchProduced_childA, ExecSparsifyChildSemantics.core_codes]
      change ExecWorklistProgram.record (natFormulaCode (codes (children w).1)) =
        ExecWorklistProgram.record (encode (children w).1)
      rw [encode_eq]
    · change (branchProduced _ _ _ _).stacks (port k 3) = _
      rw [branchProduced_childB, ExecSparsifyChildSemantics.petal_codes]
      change ExecWorklistProgram.record (natFormulaCode (codes (children w).2)) =
        ExecWorklistProgram.record (encode (children w).2)
      rw [encode_eq]
    · change (branchProduced _ _ _ _).stacks (port k 4) = []
      exact branchProduced_clean _ _ _ _ (port k 4)
        ⟨by change 4 ≤ (4 : ℕ); omega, by change (4 : ℕ) < 37; omega⟩
  · intro i hi hj
    exact branchProduced_clean _ _ _ _ i ⟨by omega, hj⟩
  · intro i hi
    rw [branchProduced_parameter _ _ _ _ i hi]
    exact after_parameter e pending leaves i hi

def finishBound (bits : ℕ) : ℕ := 1000000 * (bits + 1) ^ 2

def executionCost (e : Execution frame z F) : ℕ :=
  24 * (encode F).length + 29 + e.steps + finishBound (localSearchBits e.final) + 1

theorem word_length_le (e : Execution frame z F) (i : Fin (k + 34)) :
    (e.final.stacks i).length ≤ stackBits e.final.stacks := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le ((e.final.stacks j).length))
    (Finset.mem_univ i)

theorem child_volume_le (e : Execution frame z F)
    (hn : e.final.stacks (low k 21) ≠ []) :
    ExecBranchController.volume (codes F) (codes (witness e hn).selected)
      ((witness e hn).core.map Encoding.literalCode) ≤ 4 * stackBits e.final.stacks + 3 := by
  have hF := word_length_le e (low k 16)
  have hG := word_length_le e (low k 13)
  have hH := word_length_le e (low k 8)
  rw [e.source] at hF
  rw [(witness e hn).family_word] at hG
  rw [(witness e hn).core_word] at hH
  change (natFormulaCode (codes (witness e hn).selected)).length +
    (natFormulaCode (codes F)).length +
    2 * (natClauseCode ((witness e hn).core.map Encoding.literalCode)).length + 3 ≤ _
  omega

theorem terminal_cost_le (e : Execution frame z F) (pending leaves : List (Formula n)) :
    terminalCost (after e pending leaves) + 2 ≤ finishBound (stackBits e.final.stacks) := by
  have h := searchBits_le (encode F) (input encode frame F pending leaves 0) e.final
  unfold terminalCost finishBound
  change searchBits (after e pending leaves) ≤ stackBits e.final.stacks at h
  nlinarith [Nat.zero_le (stackBits e.final.stacks)]

theorem branch_cost_le (e : Execution frame z F) (pending leaves : List (Formula n))
    (hn : e.final.stacks (low k 21) ≠ []) :
    branchCost (after e pending leaves) (codes F) (codes (witness e hn).selected)
      ((witness e hn).core.map Encoding.literalCode) + 2 ≤ finishBound (stackBits e.final.stacks) := by
  have hl := loadCost_le (encode F) (input encode frame F pending leaves 0) e.final
  have ht := transientBits_le (encode F) (input encode frame F pending leaves 0) e.final
  have hv := Nat.pow_le_pow_left (child_volume_le e hn) 2
  change loadCost (after e pending leaves) ≤ 21 * stackBits e.final.stacks + 15 at hl
  change transientBits (after e pending leaves) ≤ stackBits e.final.stacks at ht
  unfold branchCost prepareCost finishBound
  nlinarith [Nat.zero_le (stackBits e.final.stacks)]

theorem child_volume_le_local (e : Execution frame z F)
    (hn : e.final.stacks (low k 21) ≠ []) :
    ExecBranchController.volume (codes F) (codes (witness e hn).selected)
      ((witness e hn).core.map Encoding.literalCode) ≤ 4 * localSearchBits e.final + 3 := by
  have hF := low_word_length_le e.final (16 : Fin 32)
  have hG := low_word_length_le e.final (13 : Fin 32)
  have hH := low_word_length_le e.final (8 : Fin 32)
  rw [e.source] at hF
  rw [(witness e hn).family_word] at hG
  rw [(witness e hn).core_word] at hH
  change (natFormulaCode (codes (witness e hn).selected)).length +
    (natFormulaCode (codes F)).length +
    2 * (natClauseCode ((witness e hn).core.map Encoding.literalCode)).length + 3 ≤ _
  omega

theorem terminal_cost_le_local (e : Execution frame z F) (pending leaves : List (Formula n)) :
    terminalCost (after e pending leaves) + 2 ≤ finishBound (localSearchBits e.final) := by
  have h := ExecSparsifySearchFrame.terminalCost_le_local (encode F)
    (input encode frame F pending leaves 0) e.final
  change terminalCost (after e pending leaves) ≤ 2 * localSearchBits e.final + 129 at h
  unfold finishBound
  nlinarith [Nat.zero_le (localSearchBits e.final)]

theorem branch_cost_le_local (e : Execution frame z F) (pending leaves : List (Formula n))
    (hn : e.final.stacks (low k 21) ≠ []) :
    branchCost (after e pending leaves) (codes F) (codes (witness e hn).selected)
      ((witness e hn).core.map Encoding.literalCode) + 2 ≤ finishBound (localSearchBits e.final) := by
  have hp := prepareCost_le_local (encode F) (input encode frame F pending leaves 0) e.final
  have hv := Nat.pow_le_pow_left (child_volume_le_local e hn) 2
  change prepareCost (after e pending leaves) ≤ 23 * localSearchBits e.final + 105 at hp
  unfold branchCost finishBound
  nlinarith [Nat.zero_le (localSearchBits e.final)]

theorem start_finish_eval {a b c : Data k} {s t : ℕ}
    (hs : Eval (ExecSparsifyProgram.start k) s a b)
    (ht : Eval (ExecSparsifyProgram.finish k) t b c) :
    Eval (ExecSparsifyProgram.command k) (s + t) a c := by
  change Eval (.seq (readHead k) (ExecSparsifyProgram.search k)) s a b at hs
  cases hs with
  | @seq first second u v a0 b0 c0 hhead hsearch =>
    have he : Eval (ExecSparsifyProgram.command k) (u + (v + t)) a c :=
      hhead.seq (hsearch.seq ht)
    exact (Nat.add_assoc u v t).symm ▸ he

/-- Full one-node execution, including bounded-head extraction, actual search,
actual child construction or terminal cleanup, and the final program halt. -/
theorem program_runs (e : Execution frame z F) (hf : FrameReady frame)
    (pending leaves : List (Formula n)) :
    RunsIn (ExecSparsifyProgram.program k) (executionCost e)
      ((input encode frame F pending leaves 0).withPC (some (ExecSparsifyProgram.program k).entry))
      ((ExecWorklistLoop.Ambient.liftData coreReg (coreStack k) frame
        (ExecWorklistLoop.splitData encode F pending leaves (splitAt e))).withPC none) := by
  classical
  let q := after e pending leaves
  have hs := start_eval e hf pending leaves
  have hw : q.stacks (port k 26) = e.final.stacks (low k 21) :=
    after_stack e pending leaves (low k 21)
  by_cases hn : e.final.stacks (low k 21) = []
  · have he := ExecSparsifyProgram.finish_terminal_eval q (hw.trans hn)
    have whole := start_finish_eval hs he
    have heq := terminal_output e hf pending leaves
    rw [heq] at whole
    have hsplit : splitAt e = none := by simp [splitAt, hn]
    rw [← hsplit] at whole
    refine ⟨24 * (encode F).length + 29 + e.steps + (terminalCost q + 2) + 1, ?_, ?_⟩
    · exact Nat.add_le_add_right
        (Nat.add_le_add_left (terminal_cost_le_local e pending leaves) _) 1
    · exact compiled_halt_trace whole (port k 0) (port k 2)
  · let w := witness e hn
    have hq : q.stacks (port k 26) ≠ [] := by rwa [hw]
    have hF : q.stacks (port k 21) = ExecBranchController.formulaCode (codes F) :=
      (after_stack e pending leaves (low k 16)).trans e.source
    have hG : q.stacks (port k 18) = ExecBranchController.formulaCode (codes w.selected) :=
      (after_stack e pending leaves (low k 13)).trans w.family_word
    have hH : q.stacks (port k 13) = ExecBranchController.clauseCode (w.core.map Encoding.literalCode) :=
      (after_stack e pending leaves (low k 8)).trans w.core_word
    obtain ⟨t, ht, he⟩ := ExecSparsifyProgram.finish_branch_eval q (codes F) (codes w.selected)
      (w.core.map Encoding.literalCode) hq
      (after_empty e hf pending leaves (port k 2) ⟨by change 2 ≤ (2 : ℕ); omega, by change (2 : ℕ) ≤ 7; omega⟩)
      (after_empty e hf pending leaves (port k 3) ⟨by change 2 ≤ (3 : ℕ); omega, by change (3 : ℕ) ≤ 7; omega⟩)
      (after_empty e hf pending leaves (port k 4) ⟨by change 2 ≤ (4 : ℕ); omega, by change (4 : ℕ) ≤ 7; omega⟩)
      (after_empty e hf pending leaves (port k 5) ⟨by change 2 ≤ (5 : ℕ); omega, by change (5 : ℕ) ≤ 7; omega⟩)
      (after_empty e hf pending leaves (port k 6) ⟨by change 2 ≤ (6 : ℕ); omega, by change (6 : ℕ) ≤ 7; omega⟩)
      (after_empty e hf pending leaves (port k 7) ⟨by change 2 ≤ (7 : ℕ); omega, by change (7 : ℕ) ≤ 7; omega⟩) hF hG hH
    have whole := start_finish_eval hs he
    have heq := branch_output e hf pending leaves hn
    rw [heq] at whole
    have hsplit : splitAt e = some (children w) := by simp [splitAt, hn, w]
    rw [← hsplit] at whole
    refine ⟨24 * (encode F).length + 29 + e.steps + t + 1, ?_, ?_⟩
    · have hb := branch_cost_le_local e pending leaves hn
      have ht' : t ≤ finishBound (localSearchBits e.final) := ht.trans hb
      unfold executionCost
      exact Nat.add_le_add_right (Nat.add_le_add_left ht' _) 1
    · exact compiled_halt_trace whole (port k 0) (port k 2)

/-- A genuine trace can allocate at most one bit per instruction. Applying
this only to the isolated local search avoids every worklist-tail byte. -/
theorem executionCost_le (e : Execution frame z F) :
    executionCost e ≤ 1000100 *
      (stackBits (localInput frame F).stacks + e.steps + 1) ^ 2 := by
  have hs := trace_dataBits (ExecCNFNodeSearch.program k) e.trace
  change stackBits e.final.stacks ≤ stackBits (localInput frame F).stacks + e.steps at hs
  have hl : (encode F).length ≤ stackBits (localInput frame F).stacks := by
    rw [← localInput_source frame F]
    exact ExecSparsifySearchFrame.stack_length_le _ (low k 16)
  have hlocal : localSearchBits e.final ≤ stackBits e.final.stacks :=
    list_stack_bits_le e.final.stacks _ (localSearchPorts_nodup k)
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right (hlocal.trans hs) 1) 2
  unfold executionCost finishBound
  nlinarith [Nat.zero_le (stackBits (localInput frame F).stacks), Nat.zero_le e.steps]

/-- Only the active low32 stack block enters the finish estimate. Preserved
parameter and caller cache stacks may have arbitrary lengths. -/
theorem executionCost_le_active (e : Execution frame z F) :
    executionCost e ≤ 1000100 *
      (localSearchBits (localInput frame F) + e.steps + 1) ^ 2 := by
  have hs := BitProgram.trace_listStackBits (ExecCNFNodeSearch.program k)
    (localSearchPorts k) (localSearchPorts_nodup k) e.trace
  change localSearchBits e.final ≤ localSearchBits (localInput frame F) + e.steps at hs
  have hl : (encode F).length ≤ localSearchBits (localInput frame F) := by
    rw [← localInput_source frame F]
    exact low_word_length_le _ (16 : Fin 32)
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2
  unfold executionCost finishBound
  nlinarith [Nat.zero_le (localSearchBits (localInput frame F)), Nat.zero_le e.steps]

/-- Every active input port except the copied formula is empty. This also
discharges the width driver's old-width/old-threshold cleanup allowance. -/
theorem localInput_low (hf : FrameReady frame) (i : Fin 32) :
    (localInput frame F).stacks (low k i) =
      if i = 16 then encode F else [] := by
  by_cases hi : i = 16
  · subst i
    simp
  · simp only [ite_eq_right hi]
    change (headLoaded (encode F) (input encode frame F [] [] 0)).stacks
      (ExecSparsifyProgram.searchPort k (low k i)) = []
    have hn : ExecSparsifyProgram.searchPort k (low k i) ≠ port k 21 := by
      intro he
      apply hi
      apply Fin.ext
      have hv := congrArg Fin.val he
      change 5 + i.val = 21 at hv
      omega
    rw [headLoaded_stack_frame _ _ _ hn]
    apply input_clean encode frame hf F [] [] 0
    · change 2 ≤ 5 + i.val
      omega
    · change 5 + i.val < 37
      omega

/-- At node entry the only active word is the copied current formula. -/
theorem localInput_bits (hf : FrameReady frame) :
    localSearchBits (localInput frame F) = (encode F).length :=
  localSearchBits_initial (encode F) (input encode frame F [] [] 0)
    (input_clean encode frame hf F [] [] 0)

theorem executionCost_le_body (e : Execution frame z F) (hf : FrameReady frame) :
    executionCost e ≤ 1000100 * ((encode F).length + e.steps + 1) ^ 2 := by
  simpa only [localInput_bits hf] using executionCost_le_active e

/-- A costed run of the same deterministic local program prices the chosen
observation exactly, without changing its output or candidate order. -/
theorem observed_steps_le (e : Execution frame z F) (bound : ℕ)
    (b : ExecCNFNodeSearch.Data k)
    (h : RunsIn (ExecCNFNodeSearch.program k) bound
      ((localInput frame F).withPC (some (ExecCNFNodeSearch.program k).entry))
      (b.withPC none)) : e.steps ≤ bound := by
  exact (SparsifyIntegrity.terminal_trace_le_of_runsIn e.trace h
    (step_none _ _ rfl) (step_none _ _ rfl)).1

theorem executionCost_le_of_runsIn (e : Execution frame z F) (bound : ℕ)
    (b : ExecCNFNodeSearch.Data k)
    (h : RunsIn (ExecCNFNodeSearch.program k) bound
      ((localInput frame F).withPC (some (ExecCNFNodeSearch.program k).entry))
      (b.withPC none)) :
    executionCost e ≤ 1000100 *
      (stackBits (localInput frame F).stacks + bound + 1) ^ 2 := by
  apply (executionCost_le e).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have ht := observed_steps_le e bound b h
  omega

theorem executionCost_le_body_of_runsIn (e : Execution frame z F) (hf : FrameReady frame)
    (bound : ℕ) (b : ExecCNFNodeSearch.Data k)
    (h : RunsIn (ExecCNFNodeSearch.program k) bound
      ((localInput frame F).withPC (some (ExecCNFNodeSearch.program k).entry))
      (b.withPC none)) :
    executionCost e ≤ 1000100 * ((encode F).length + bound + 1) ^ 2 := by
  apply (executionCost_le_body e hf).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have ht := observed_steps_le e bound b h
  omega

/-- The local execution choice precedes both arbitrary worklist streams. -/
noncomputable def cost (frame : Data k) (z : ℕ → ℕ) (hf : FrameReady frame)
    (hb : BankValues z frame) (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) : ℕ := by
  classical
  exact if hF : Ready k F then executionCost (observe frame z hf hb hz F hF) else 0

theorem realizes (frame : Data k) (z : ℕ → ℕ) (hf : FrameReady frame)
    (hb : BankValues z frame) (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) :
    ExecWorklistLoop.Ambient.BoundedRealizesOn (ExecSparsifyProgram.program k)
      coreReg (coreStack k) frame encode
      (branching (n := n) frame z hf hb hz).split (Ready k) (cost frame z hf hb hz) := by
  intro F hF pending leaves
  have h := program_runs (observe frame z hf hb hz F hF) hf pending leaves
  simpa only [branching, ExecSparsifyObserved.split, cost, dite_eq_left hF,
    input] using h

end SubexponentialSAT.ExecSparsifyExecution

end OAI.Algorithms
