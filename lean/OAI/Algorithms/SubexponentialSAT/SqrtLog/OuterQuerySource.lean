import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStart
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramExpansion
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesOrigin

namespace OAI.Algorithms

/-! Exact typed formula, raw-row and padded-word provenance for the native
query frontend. These definitions describe already-produced bytes. -/
namespace SubexponentialSAT.SqrtLog.OuterQuery
open SubexponentialSAT BitProgram StructuredCalls
open LeafOuterProgram

abbrev Formula (n : ℕ) := ExecCNF.Formula (SAT.Literal (Fin n))

def sourceClause {n : ℕ} (F : Formula n) (i : Fin (formulaRecords F).length) :=
  F[i.val]'(by simpa only [formulaRecords_length] using i.isLt)

def sourceCodes {n : ℕ} (F : Formula n) (i : Fin (formulaRecords F).length) : List ℕ :=
  (sourceClause F i).map Encoding.literalCode

theorem source_encoding {n : ℕ} (F : Formula n) :
    formulaRecords F=HashInputProgram.Expansion.encodedClauses F := rfl

theorem source_codes {n : ℕ} (F : Formula n) (i : Fin (formulaRecords F).length) :
    (formulaRecords F)[i.val]=Encoding.encodeList Encoding.encodeNat (sourceCodes F i) := by
  simp only [formulaRecords, List.getElem_map]
  exact HashInputProgram.clausePayload_codes (sourceClause F i)

theorem source_width {n k : ℕ} (F : Formula n)
    (h : ∀ C ∈ F, C.length ≤ k) (i : Fin (formulaRecords F).length) :
    (sourceCodes F i).length ≤ k := by
  rw [sourceCodes,List.length_map]
  exact h _ (List.getElem_mem _)

theorem source_id_lt {n : ℕ} (F : Formula n) (i : Fin (formulaRecords F).length)
    (c : ℕ) (hc : c ∈ sourceCodes F i) : c/2 < n := by
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hc
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by
    simpa only [Nat.mul_comm] using Encoding.literalCode_lt l)

def markIndex {m : ℕ} (mark : Option (Fin m)) : List Bool :=
  match mark with | none => [false] | some i => Encoding.encodeNat i.val

def query {n : ℕ} (F : Formula n) (a : Data)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) : LeafQueryFrontend.Query where
  clauses := formulaRecords F
  codes := sourceCodes F
  rows := rows
  mark := mark
  index := markIndex mark
  width := a.stacks 783
  modulus := a.stacks 782
  ambient := a.stacks 785

theorem query_valid {n B : ℕ} (F : Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B) (hm : 0 < (formulaRecords F).length)
    (hn : 0 < n) (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) : (query F a rows mark).Valid := by
  have hc : CounterPrograms.value (a.stacks 783)=3*(formulaRecords F).length := by
    rw [ha.width,CounterPrograms.value_eq_toNat,ha.count]
  have hwidth := (HashFamilyPayload.countWord_width_sufficient (a.stacks 783) hc).le
  refine ⟨HashFamilyPayload.width_pos hm hwidth,?_,source_codes F,hwidth,?_,ha.clauses,?_⟩
  · change 0 < BinaryArithmetic.toNat (a.stacks 785)
    rw [ha.ambient]; exact hn
  · intro i hi
    change markIndex mark=Encoding.encodeNat i.val
    change mark=some i at hi
    rw [hi]
    rfl
  · intro row hr v hv
    change row ∈ HashScopeProgram.Complete.scopes 1 0 (sourceCodes F) rows mark at hr
    rw [HashScopeProgram.Complete.scopes,List.mem_append] at hr
    change v < BinaryArithmetic.toNat (a.stacks 785)
    rw [ha.ambient]
    rcases hr with hr | hr
    · obtain ⟨terms,hterms,rfl⟩ := List.mem_map.mp hr
      obtain ⟨term,hterm,c,hc,rfl⟩ := (HashScopeProgram.FromTuple.mem_interpreted_scope 1 0 _ _ _).mp hv
      exact source_id_lt F term.1 c hc
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
      obtain ⟨c,hc,he⟩ := (SubexpScopeProducer.mem_scope [true] (sourceCodes F i) v).mp hv
      have hh : c/2=v := by simpa [BinaryArithmetic.toNat,BinaryArithmetic.bitVal_true] using he
      rw [←hh]
      exact source_id_lt F i c hc

theorem query_source {n : ℕ} (F : Formula n) (a : Data)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) :
    (query F a rows mark).clauses=HashInputProgram.Expansion.encodedClauses F := rfl

theorem query_ambient {n B : ℕ} (F : Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) :
    ProducedQueryResources.ambient (query F a rows mark)=n := ha.ambient

end SubexponentialSAT.SqrtLog.OuterQuery

end OAI.Algorithms
