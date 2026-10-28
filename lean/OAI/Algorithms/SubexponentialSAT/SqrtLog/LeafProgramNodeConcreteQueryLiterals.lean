import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteQueryScope
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcrete

namespace OAI.Algorithms

/-! The exact weighted clauses supplied to the native factor interpreter
inherit their low-literal incidence entries from the original query. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT HashInputProgram
open HashCircuitProgram HashCircuitProgram.Native

variable (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))))
    (hs : q.clauses=Expansion.encodedClauses source)

def queryWeightedHashes (t d : ℕ) :=
  (PreparedSource.castRows (congrArg List.length hs) q.rows).map
    (Expansion.weightedRow t d source)

include hv in
 theorem query_weighted_literal_present (t d id : ℕ)
    (hi : id < (queryWeightedHashes q source hs t d).length)
    (w : Row.WeightedClause (BinaryArithmetic.toNat q.ambient) (SubexpLiftRing.baseWidth 3 t) d)
    (hw : w∈(queryWeightedHashes q source hs t d)[id])
    (l : SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient))) (hl : l∈w.literals)
    (hlow : q.forward.getD l.variable.val false=false) :
    (l.variable.val,BinaryArithmetic.toNat q.ambient+id)∈
      PackingIncidenceInput.addressedEntries q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward := by
  have hid : id < q.rows.length := by simpa [queryWeightedHashes,PreparedSource.castRows] using hi
  simp only [queryWeightedHashes,PreparedSource.castRows,List.getElem_map,Expansion.weightedRow,
    List.map_map,Function.comp_def] at hw
  obtain ⟨term,ht,rfl⟩ := List.mem_map.mp hw
  exact query_hash_literal_present q hv source hs id hid term ht l hl hlow

include hv hs in
 theorem query_marked_clause_present (hm : q.mark.isSome=true)
    (l : SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))
    (hl : l∈source[PreparedSource.markIndex q]?.getD [])
    (hlow : q.forward.getD l.variable.val false=false) :
    (l.variable.val,BinaryArithmetic.toNat q.ambient+q.rows.length)∈
      PackingIncidenceInput.addressedEntries q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward := by
  cases hq : q.mark with
  | none => simp [hq] at hm
  | some i =>
    have hi : i.val < source.length := by simpa only [hs,Expansion.encodedClauses,List.length_map] using i.isLt
    have hmidx : PreparedSource.markIndex q=i.val := by simp [PreparedSource.markIndex,hq]
    rw [hmidx] at hl
    have hli : l∈Expansion.originalClause source (Fin.cast (congrArg List.length hs) i) := by
      simpa [List.getElem?_eq_getElem hi,Expansion.originalClause] using hl
    exact query_marked_literal_present q hv source hs i hq l hli hlow

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
