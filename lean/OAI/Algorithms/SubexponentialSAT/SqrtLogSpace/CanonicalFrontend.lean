import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CanonicalInput
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram

/-! The actual canonical normalizer emits the ordered body consumed by the
disjoint DFS. Both sides retain the declared ambient variable universe. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem canonical_normalized_formula {n : ℕ} (F : SAT.CNF (Fin n)) :
    SubexpNormalizationCorrectness.normalizedFormula F =
      ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F) :=
  ExecCNFCodeTransport.normalizedInput_eq_normalize _

theorem canonical_normalized_body {n : ℕ} (F : SAT.CNF (Fin n)) :
    SubexpNormalizationCorrectness.normalizedBody F =
      DisjointReuse.SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate
        (ExecQuantitativeSparsify.formulaList F)) := by
  unfold SubexpNormalizationCorrectness.normalizedBody
  rw [canonical_normalized_formula]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
