import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawBoot
import OAI.Algorithms.SubexponentialSAT.SubexpMainAssembly

namespace OAI.Algorithms

/-!
# Record facts for the actual ordered-input boot

The records are the leaves produced by this boot, with their existing encoding.
The input remains an ordered clause list; satisfiability uses its formula set.
-/

namespace SubexponentialSAT.SubexpOrderedRawRecordFacts

open SubexpMainProgram SubexpSetupProgram

variable {cfg : Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
  {F : SubexpOrderedRawPrefix.Formula n}

theorem valid_leaf (run : SubexpOrderedRawBoot.Run cfg hr F)
    (G : SubexpLeafSemantics.Leaf n) (hG : G ∈ run.leaves) :
    SubexpMainAssembly.validLeaf cfg n G := by
  have hc := run.outcome.correct.clause_nodup G hG
  have hl := run.outcome.correct.literal_nodup G hG
  have hw := run.outcome.correct.width G hG
  refine ⟨⟨hc, hw, run.outcome.correct.occurrence G hG⟩, hc, hl, ?_⟩
  intro C hC
  have hwidth := hw (ExecCNF.clauseSet C) (ExecCNF.mem_formulaSet.mpr ⟨C, hC, rfl⟩)
  simpa only [ExecCNF.clauseSet, List.toFinset_card_of_nodup (hl C hC)] using hwidth

theorem records_eq (run : SubexpOrderedRawBoot.Run cfg hr F) :
    run.records = run.leaves.map ExecQuantitativeSparsify.encodeRawFormula := by
  apply List.map_congr_left
  intro G _
  exact ExecSparsifyEncoding.words_encodeRawFormula G

theorem valid_records (run : SubexpOrderedRawBoot.Run cfg hr F) :
    ∀ bits ∈ run.records,
      SubexpLeafSemantics.validPayload n (SubexpMainAssembly.validLeaf cfg n) bits := by
  intro bits hb
  rw [records_eq] at hb
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hb
  exact ⟨G, valid_leaf run G hG, rfl⟩

theorem correct (run : SubexpOrderedRawBoot.Run cfg hr F) :
    run.records.any (SubexpLeafSemantics.test n) = true ↔
      SAT.Satisfiable (ExecCNF.formulaSet F) := by
  rw [records_eq]
  exact (SubexpLeafContract.records_any_test run.leaves).trans run.satisfiable.symm

end SubexponentialSAT.SubexpOrderedRawRecordFacts

end OAI.Algorithms
