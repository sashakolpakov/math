import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryCountPrepared

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.OuterQuery.Count
open LeafProgram LeafOuterProgram
open scoped BigOperators
noncomputable section

private theorem sum_fin_cast {m M : ℕ} (h : m=M) (f : Fin M → ℕ) :
    (∑ i : Fin m, f (Fin.cast h i))=∑ i : Fin M,f i := by
  subst M
  rfl

theorem selectorCount_none {n : ℕ} (F : Formula n) (width : ℕ) (payloads : List (List Bool)) :
    selectorCount F width payloads none =
    HashSelect.acceptedCount (HashSelect.cnfRowAccept (formulaClauses F))
      (payloads.map (HashFamilyPayload.decodeVariableRow F.length width)) := rfl

theorem selectorCount_some {n : ℕ} (F : Formula n) (width : ℕ) (payloads : List (List Bool))
    (i : Fin (formulaRecords F).length) :
    selectorCount F width payloads (some i) =
    markedCount (HashSelect.cnfRowAccept (formulaClauses F))
      (payloads.map (HashFamilyPayload.decodeVariableRow F.length width))
      (fun e x => !(formulaClauses F e).eval x) (Fin.cast (formulaRecords_length F) i) := rfl

theorem sum_selectorCount {n : ℕ} (F : Formula n) (width : ℕ) (payloads : List (List Bool)) :
    (∑ i : Fin (formulaRecords F).length,selectorCount F width payloads (some i)) =
    HashSelect.mass (HashSelect.cnfRowAccept (formulaClauses F))
      (HashInput.violationWeight (formulaClauses F))
      (payloads.map (HashFamilyPayload.decodeVariableRow F.length width)) := by
  simp only [selectorCount_some]
  rw [sum_fin_cast]
  exact sum_marked_cnf _ _ _

end
end SubexponentialSAT.SqrtLog.OuterQuery.Count

end OAI.Algorithms
