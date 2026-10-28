import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram

/-! Append the actual positivity scan to a proved exact-count execution.
Both outputs, the time charge and every source-prefix bound belong to this
same command; the count word is preserved in full. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse

theorem answer_bounded (a : State 80 1220) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    DFSVisit.BoundedEval answerCommand (answerSteps a - 1) a (answerResult a)
      (1232 * bound + 15) := by
  refine ⟨answerCommand_eval a, ?_⟩
  intro steps b hs ht i
  exact answer_all_prefix a bound ha steps b (hs.trans (Nat.sub_le _ _)) ht i

theorem append_answer {n : ℕ} (F : SAT.CNF (Fin n))
    (body : Cmd 80 1220) {steps : ℕ} {a b : State 80 1220} {bound : ℕ}
    (hbody : DFSVisit.BoundedEval body steps a b bound)
    (hcount : b.stacks ABI.countStack = countWord (SAT.count F)) :
    ∃ total, total ≤ steps + 12 * bound + 14 ∧
      DFSVisit.BoundedEval (.seq body answerCommand) total a (answerResult b)
        (1232 * bound + 15) ∧
      (answerResult b).stacks ABI.countStack = countWord (SAT.count F) ∧
      (answerResult b).stacks ABI.answerStack = [decide (0 < SAT.count F)] ∧
      (decide (0 < SAT.count F) = true ↔ SAT.Satisfiable F) := by
  have hb := hbody.final_bound
  have hseq := (DFSCountProgram.boundedEval_mono hbody (by omega)).seq
    (answer_bounded b bound hb)
  refine ⟨steps + (answerSteps b - 1), ?_, hseq, ?_, ?_, ?_⟩
  · have hc := hb ABI.countStack
    have ha := hb ABI.answerStack
    have hs := hb ABI.positivityScratch
    dsimp only [answerSteps]
    omega
  · exact (answerResult_count b).trans hcount
  · rw [answerResult_answer, hcount, countWord_toNat]
  · simp [SAT.count_pos_iff]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
