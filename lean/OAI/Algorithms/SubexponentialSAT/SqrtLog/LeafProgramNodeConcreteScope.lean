import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramComplete
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputAddressed
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsOwners

namespace OAI.Algorithms

/-! Every queried low literal is in the physical raw-scope incidence list.
Zero coefficients and repeated literal occurrences are retained. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT
open HashInputProgram HashScopeProgram

variable {n : ℕ}

theorem encoded_clause_codes (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i,clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (source : List (List (SAT.Literal (Fin n))))
    (hs : clauses=Expansion.encodedClauses source) (i : Fin clauses.length) :
    codes i=(Expansion.originalClause source (Fin.cast (congrArg List.length hs) i)).map Encoding.literalCode := by
  subst clauses
  apply Encoding.encodeList_injective Encoding.encodeNat_injective
  rw [←hc,←HashInputProgram.clausePayload_codes]
  simp only [Expansion.originalClause,Expansion.encodedClauses,List.getElem_map]
  rfl

theorem literal_mem_raw_scope (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (source : List (List (SAT.Literal (Fin n))))
    (hs : clauses=Expansion.encodedClauses source)
    (hc : ∀ i,clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3)) (term : Fin clauses.length × ZMod 3)
    (ht : term∈terms) (l : SAT.Literal (Fin n))
    (hl : l∈Expansion.originalClause source (Fin.cast (congrArg List.length hs) term.1)) :
    l.variable.val∈scope (FromTuple.interpretedTerms (clauses:=clauses) 1 0 codes terms) := by
  apply (FromTuple.mem_interpreted_scope 1 0 codes terms l.variable.val).mpr
  refine ⟨term,ht,Encoding.literalCode l,?_,SubexpLeafSemantics.literalCode_div_two l⟩
  rw [encoded_clause_codes clauses codes hc source hs]
  exact List.mem_map.mpr ⟨l,hl,rfl⟩

theorem literal_mem_marked_scope (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (source : List (List (SAT.Literal (Fin n))))
    (hs : clauses=Expansion.encodedClauses source)
    (hc : ∀ i,clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (i : Fin clauses.length) (l : SAT.Literal (Fin n))
    (hl : l∈Expansion.originalClause source (Fin.cast (congrArg List.length hs) i)) :
    l.variable.val∈Marked.markedScope (codes i) := by
  rw [SubexpScopeProducer.mem_scope]
  refine ⟨Encoding.literalCode l,?_,?_⟩
  · rw [encoded_clause_codes clauses codes hc source hs]
    exact List.mem_map.mpr ⟨l,hl,rfl⟩
  · simpa [BinaryArithmetic.toNat] using SubexpLeafSemantics.literalCode_div_two l

theorem addressed_original_present (scopes : List (List ℕ)) (mask : List Bool)
    (ambient owner factor : ℕ) (ho : owner∈LeafStatisticsSemantics.lowOwners 0 mask)
    (hf : factor < scopes.length) (hs : owner∈scopes[factor]) :
    (owner,ambient+factor)∈PackingIncidenceInput.addressedEntries scopes ambient mask := by
  apply List.mem_map.mpr
  refine ⟨(owner,factor),?_,rfl⟩
  apply (LeafStatisticsSemantics.native_original_mem scopes mask 0 scopes.length owner factor le_rfl hf).mpr
  refine ⟨ho,?_⟩
  change factor∈Subexp.IncidencePlanSpec.incidentIndices scopes owner
  exact (Subexp.IncidencePlanSpec.mem_incidentIndices scopes owner ⟨factor,hf⟩).mpr hs

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
