import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryOrigin
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsGenerated
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramMarkedTable

namespace OAI.Algorithms

/-! Literal byte equality between parser records and the raw-table frontend.
These equalities retain zero coefficients and repeated coordinates. -/
namespace SubexponentialSAT.SqrtLog.OuterQuery
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram LeafScopeResourceBounds
open LeafOuterProgram

noncomputable section

theorem available_roundtrip {n B : ℕ} (F : Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (hm : 0 < (formulaRecords F).length)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (seed : List Bool) (rest : Records)
    (hf : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom (formulaRecords F).length B)=seed::rest)
    (bits : List Bool) (hb : bits ∈ seed::rest ∨ bits ∈ initial F a s Q) :
    (CodeRowsProgram.rowPayload (a.stacks 783).length (formulaRecords F).length
      (rawDecode (formulaRecords F).length (a.stacks 783).length hm bits)).reverse=bits := by
  have hc : CounterPrograms.value (a.stacks 783)=3*(formulaRecords F).length := by
    rw [ha.width,CounterPrograms.value_eq_toNat,ha.count]
  have hw := (HashFamilyPayload.countWord_width_sufficient (a.stacks 783) hc).le
  rcases hb with hb | hb
  · apply rawDecode_generated_payload hm hw bits
    rw [←HashFamilyPayload.alphabetWords_eq (a.stacks 783) hc,ha.width,hf]
    exact hb
  · obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hb
    rw [rawDecode_rowPayload hm hw]

theorem trial_encoding {n B : ℕ} (F : Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (hm : 0 < (formulaRecords F).length)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest : Records)
    (hf : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom (formulaRecords F).length B)=seed::rest)
    (round : ℕ) (bits : List Bool) (hb : bits ∈ seed::rest) :
    candidateEncoding (bits::selected score seed rest (initial F a s Q) round)=
      HashScopeProgram.RawTable.inputBits (a.stacks 783).length
        (trialRows F a hm s Q score seed rest round bits) := by
  rw [HashScopeProgram.Complete.inputBits_codeRows]
  apply raw_records_encoding hm
  intro p hp
  apply available_roundtrip F a ha hm s Q seed rest hf p
  rcases List.mem_cons.mp hp with hp | hp
  · exact Or.inl (hp ▸ hb)
  · exact selected_mem score seed rest (initial F a s Q) round p hp

theorem final_encoding {n B : ℕ} (F : Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (hm : 0 < (formulaRecords F).length)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest : Records)
    (hf : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom (formulaRecords F).length B)=seed::rest) :
    candidateEncoding (selected score seed rest (initial F a s Q)
      (HashSelect.loopCap n (formulaRecords F).length))=
      HashScopeProgram.RawTable.inputBits (a.stacks 783).length
        (finalRows F a hm s Q score seed rest) := by
  rw [HashScopeProgram.Complete.inputBits_codeRows]
  apply raw_records_encoding hm
  intro p hp
  exact available_roundtrip F a ha hm s Q seed rest hf p
    (selected_mem score seed rest (initial F a s Q) _ p hp)

end
end SubexponentialSAT.SqrtLog.OuterQuery

end OAI.Algorithms
