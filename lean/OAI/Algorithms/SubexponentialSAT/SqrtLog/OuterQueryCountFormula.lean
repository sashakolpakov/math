import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryCountCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryTypedSource

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.OuterQuery.Count
open LeafProgram LeafOuterProgram
noncomputable section

variable {n m : ℕ}

def indexedSource (F : Formula n) (h : m=F.length) (i : Fin m) :
    List (SAT.Literal (Fin n)) := F[Fin.cast h i]

def selectorCount (F : Formula n) (width : ℕ) (payloads : List (List Bool))
    (mark : Option (Fin (formulaRecords F).length)) : ℕ :=
  match mark with
  | none => HashSelect.acceptedCount (HashSelect.cnfRowAccept (formulaClauses F))
      (payloads.map (HashFamilyPayload.decodeVariableRow F.length width))
  | some i => markedCount (HashSelect.cnfRowAccept (formulaClauses F))
      (payloads.map (HashFamilyPayload.decodeVariableRow F.length width))
      (fun e x => !(formulaClauses F e).eval x) (Fin.cast (formulaRecords_length F) i)

theorem fullCount_formula_none (F : Formula n) (h : m=F.length)
    (width : ℕ) (hm : 0 < m) (payloads : List (List Bool))
    (clause : List (SAT.Literal (Fin n))) :
    PreparedBranchCount.fullCount
      (rawHashes (indexedSource F h) (payloads.map (LeafScopeResourceBounds.rawDecode m width hm)))
      false clause = HashSelect.acceptedCount (HashSelect.cnfRowAccept (formulaClauses F))
        (payloads.map (HashFamilyPayload.decodeVariableRow F.length width)) := by
  subst m
  exact fullCount_payload_none (indexedSource F rfl) width hm payloads clause

theorem fullCount_formula_marked (F : Formula n) (h : m=F.length)
    (width : ℕ) (hm : 0 < m) (payloads : List (List Bool)) (i : Fin m) :
    PreparedBranchCount.fullCount
      (rawHashes (indexedSource F h) (payloads.map (LeafScopeResourceBounds.rawDecode m width hm)))
      true (indexedSource F h i) = markedCount (HashSelect.cnfRowAccept (formulaClauses F))
        (payloads.map (HashFamilyPayload.decodeVariableRow F.length width))
        (fun e x => !(formulaClauses F e).eval x) (Fin.cast h i) := by
  subst m
  exact fullCount_payload_marked (indexedSource F rfl) width hm payloads i

end
end SubexponentialSAT.SqrtLog.OuterQuery.Count

end OAI.Algorithms
