import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpClauseFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLeafData

namespace OAI.Algorithms

/-!
# The physically emitted clause scope and the semantic factor scope

The raw producer and typed leaf use the same last-occurrence order. Their
equality follows from the exact emitted numeric codes, so the table and
incidence clients need not assume a separate scope-membership oracle.
-/

namespace SubexponentialSAT.SubexpClauseScopeCorrectness

open SubexpClauseFactorProgram

variable {n : ℕ}

theorem scopeOf_eq_clauseScope (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hell : 0 < BinaryArithmetic.toNat c.binaryEll)
    (hv : Valid c (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll)) ls) :
    scopeOf c ls hv = SubexpLeafData.clauseScope
      (ChunkPartition.indexEquiv n (BinaryArithmetic.toNat c.binaryEll) hell) ls := by
  apply List.map_injective_iff.mpr Fin.val_injective
  rw [scopeOf_values, SubexpLeafData.clauseScope_codes hell ls]
  rfl

/-- Exact membership needed by the ranked-table adapter, derived from the
canonical packing and the actual literal list. -/
theorem scopeOf_mem_cnfScope (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hell : 0 < BinaryArithmetic.toNat c.binaryEll)
    (hv : Valid c (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll)) ls)
    (F : SAT.CNF (Fin n)) (e : {C // C ∈ F}) (hliterals : ls.toFinset = e.val)
    (j : Fin (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll))) :
    j ∈ scopeOf c ls hv ↔ j ∈ FactorReduction.cnfScope
      (ChunkPartition.indexEquiv n (BinaryArithmetic.toNat c.binaryEll) hell) F e := by
  rw [scopeOf_eq_clauseScope c ls hell hv, SubexpLeafData.clauseScope,
    ExecCNF.mem_dedupLiterals, FactorReduction.cnfScope, ← hliterals]
  simp only [List.mem_map, Finset.mem_image, List.mem_toFinset]

/-- The encoded scope itself agrees, including coordinate order. -/
theorem scopeBytes_eq_canonical (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hell : 0 < BinaryArithmetic.toNat c.binaryEll)
    (hv : Valid c (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll)) ls) :
    scopeBytes c ls = Encoding.encodeList Encoding.encodeNat
      ((SubexpLeafData.clauseScope
        (ChunkPartition.indexEquiv n (BinaryArithmetic.toNat c.binaryEll) hell) ls).map Fin.val) := by
  rw [← scopeOf_eq_clauseScope c ls hell hv, scopeOf_values]
  rfl

end SubexponentialSAT.SubexpClauseScopeCorrectness

end OAI.Algorithms
