import OAI.Algorithms.SubexponentialSAT.ExecQuantitativeSparsify
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CNFNormalize
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.EncodingBounds

/-! The canonical input is already the declared-variable raw input of the
disjoint counting machine. Normalization preserves its exact ambient count. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open DisjointReuse

theorem canonical_counting_input {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) :
    encodeRawCNF (ExecQuantitativeSparsify.formulaList F) = Encoding.encodeCNF F ∧
    rawCount (ExecCNF.normalize SAT.Literal.negate
      (ExecQuantitativeSparsify.formulaList F)) = SAT.count F ∧
    (∀ C ∈ ExecCNF.normalize SAT.Literal.negate
      (ExecQuantitativeSparsify.formulaList F), C.length ≤ k) ∧
    (ExecCNF.normalize SAT.Literal.negate
      (ExecQuantitativeSparsify.formulaList F)).length ≤ F.card := by
  refine ⟨ExecQuantitativeSparsify.encodeCNF_formulaList F, ?_, ?_, ?_⟩
  · rw [rawCount_normalize, rawCount, ExecQuantitativeSparsify.formulaList_set]
  · exact normalize_width_le _ (ExecQuantitativeSparsify.formulaList_width F k hw)
  · simpa using ExecCNF.normalize_length_le SAT.Literal.negate
      (ExecQuantitativeSparsify.formulaList F)

theorem canonical_counting_output {n : ℕ} (F : SAT.CNF (Fin n)) :
    binaryNat (rawCount (ExecCNF.normalize SAT.Literal.negate
      (ExecQuantitativeSparsify.formulaList F))) = countWord (SAT.count F) := by
  rw [rawCount_normalize, rawCount, ExecQuantitativeSparsify.formulaList_set]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
