import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeQuerySize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryCountMass
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeMeaning

namespace OAI.Algorithms

/-! The physically generated reverse-order unary reference stream is tied to
exact typed marked queries. These are proof-level decoders of existing bytes. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT LeafOuterProgram
noncomputable section

 def referenceMark {m : ℕ} (hm : 0 < m) (bits : List Bool) : Fin m :=
  ⟨(bits.length-1)%m,Nat.mod_lt _ hm⟩

 def ValidReference {m : ℕ} (hm : 0 < m) (bits : List Bool) : Prop :=
  bits=Encoding.encodeNat (referenceMark hm bits).val

 theorem referenceMark_encode {m : ℕ} (hm : 0 < m) (i : Fin m) :
    referenceMark hm (Encoding.encodeNat i.val)=i := by
  apply Fin.ext
  simp [referenceMark,Nat.mod_eq_of_lt i.isLt]

 theorem validReference_encode {m : ℕ} (hm : 0 < m) (i : Fin m) :
    ValidReference hm (Encoding.encodeNat i.val) := by
  simp [ValidReference,referenceMark_encode]

 theorem alphabet_validReferences {m : ℕ} (hm : 0 < m) :
    ∀ bits∈RowSelectionProgram.Index.alphabet m, ValidReference hm bits := by
  intro bits hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi' : i < m := List.mem_range.mp (List.mem_reverse.mp hi)
  exact validReference_encode hm ⟨i,hi'⟩

 def referenceCount {n : ℕ} (F : OuterQuery.Formula n)
    (hm : 0 < (formulaRecords F).length) (width : ℕ)
    (rows : List (List Bool)) (bits : List Bool) : ℕ :=
  OuterQuery.Count.selectorCount F width rows (some (referenceMark hm bits))

 theorem referenceCount_sum {n : ℕ} (F : OuterQuery.Formula n)
    (hm : 0 < (formulaRecords F).length) (width : ℕ) (rows : List (List Bool)) :
    ((RowSelectionProgram.Index.alphabet (formulaRecords F).length).map
      (referenceCount F hm width rows)).sum =
      HashSelect.mass (HashSelect.cnfRowAccept (formulaClauses F))
        (HashInput.violationWeight (formulaClauses F))
        (rows.map (HashFamilyPayload.decodeVariableRow F.length width)) := by
  rw [LeafOuterNative.reference_sum]
  simp only [referenceCount,referenceMark_encode]
  exact OuterQuery.Count.sum_selectorCount F width rows

 theorem reference_query_index {n : ℕ} (F : OuterQuery.Formula n) (a : Data)
    (hm : 0 < (formulaRecords F).length)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length) (bits : List Bool)
    (hb : ValidReference hm bits) :
    (OuterQuery.query F a rows (some (referenceMark hm bits))).index=bits := hb.symm

 theorem query_index_length_le {n : ℕ} (F : OuterQuery.Formula n) (a : Data)
    (hm : 0 < (formulaRecords F).length)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) :
    (OuterQuery.query F a rows mark).index.length ≤ (formulaRecords F).length := by
  cases mark with
  | none =>
    simp only [OuterQuery.query,OuterQuery.markIndex,List.length_singleton]
    omega
  | some i =>
    simp only [OuterQuery.query,OuterQuery.markIndex,Encoding.length_encodeNat]
    exact Nat.succ_le_of_lt i.isLt

end
end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
