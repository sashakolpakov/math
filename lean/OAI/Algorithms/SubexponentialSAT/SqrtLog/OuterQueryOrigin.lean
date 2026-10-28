import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQuerySource

namespace OAI.Algorithms

/-! Exact origin witnesses for every trial and the final selected table.
The actual padded count word is retained; losing trials need no separate
assumption and every optional clause mark uses the same origin witness. -/
namespace SubexponentialSAT.SqrtLog.OuterQuery
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram LeafScopeResourceBounds
open LeafOuterProgram

noncomputable section

def initial {n B : ℕ} (F : Formula n) (a : Data)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B) : Records :=
  initialPayloads (a.stacks 783).length
    (CodeRowsProgram.serializedRows (formulaRecords F).length s Q)

def trialRows {n B : ℕ} (F : Formula n) (a : Data)
    (hm : 0 < (formulaRecords F).length)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest : Records)
    (round : ℕ) (bits : List Bool) :=
  trial (rawDecode (formulaRecords F).length (a.stacks 783).length hm)
    score seed rest (initial F a s Q) round bits

def finalRows {n B : ℕ} (F : Formula n) (a : Data)
    (hm : 0 < (formulaRecords F).length)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest : Records) :=
  (selected score seed rest (initial F a s Q) (HashSelect.loopCap n (formulaRecords F).length)).map
    (rawDecode (formulaRecords F).length (a.stacks 783).length hm)

private theorem query_clause_length {n : ℕ} (F : Formula n) (a : Data)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) :
    (query F a rows mark).clauses.length = (formulaRecords F).length := by
  rw [query_source]
  rfl

def trial_origin {n k B : ℕ} (F : Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (hm : 0 < (formulaRecords F).length) (hk : ∀ C ∈ F, C.length ≤ k)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest : Records)
    (hf : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom (formulaRecords F).length B)=seed::rest)
    (round : ℕ) (hr : round ≤ HashSelect.loopCap n (formulaRecords F).length)
    (bits : List Bool) (hb : bits ∈ seed::rest)
    (mark : Option (Fin (formulaRecords F).length)) :
    ProducedQueryResources.Origin (query F a (trialRows F a hm s Q score seed rest round bits) mark) k B := by
  refine ⟨hm,source_width F hk,s,Q,a.stacks 783,score,seed,rest,?_,?_,?_⟩
  · change CounterPrograms.value (a.stacks 783)=3*(formulaRecords F).length
    rw [ha.width,CounterPrograms.value_eq_toNat,ha.count]
  · rw [query_clause_length]
    simpa only [ha.width] using hf
  · left
    refine ⟨round,bits,?_,hb,rfl⟩
    rw [query_ambient F a ha, query_clause_length]
    exact hr

def final_origin {n k B : ℕ} (F : Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (hm : 0 < (formulaRecords F).length) (hk : ∀ C ∈ F, C.length ≤ k)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest : Records)
    (hf : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom (formulaRecords F).length B)=seed::rest)
    (mark : Option (Fin (formulaRecords F).length)) :
    ProducedQueryResources.Origin (query F a (finalRows F a hm s Q score seed rest) mark) k B := by
  refine ⟨hm,source_width F hk,s,Q,a.stacks 783,score,seed,rest,?_,?_,?_⟩
  · change CounterPrograms.value (a.stacks 783)=3*(formulaRecords F).length
    rw [ha.width,CounterPrograms.value_eq_toNat,ha.count]
  · rw [query_clause_length]
    simpa only [ha.width] using hf
  · right
    simp only [query_ambient F a ha]
    rfl

end
end SubexponentialSAT.SqrtLog.OuterQuery

end OAI.Algorithms
