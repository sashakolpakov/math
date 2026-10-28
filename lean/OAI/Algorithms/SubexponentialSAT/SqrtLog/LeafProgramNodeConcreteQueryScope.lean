import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteScope

namespace OAI.Algorithms

/-! Query-level incidence coverage follows from the native raw scope parser.
A fixed high literal needs no incidence; every low queried literal has one. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT HashInputProgram HashScopeProgram

variable (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))))
    (hs : q.clauses=Expansion.encodedClauses source)

theorem query_lowOwner (v : Fin (BinaryArithmetic.toNat q.ambient))
    (hlow : q.forward.getD v.val false=false) :
    v.val∈LeafStatisticsSemantics.lowOwners 0 q.forward := by
  have hlen : q.forward.length=BinaryArithmetic.toNat q.ambient := by
    simp [LeafQueryFrontend.Query.forward,LeafQueryFrontend.highMask]
  have hb : v.val < q.forward.length := by omega
  apply (LeafStatisticsSemantics.lowOwners_mem 0 v.val q.forward).mpr
  refine ⟨⟨v.val,hb⟩,by simp,?_⟩
  simpa only [List.getD_eq_getElem _ _ hb,List.get_eq_getElem] using hlow

include hv in
theorem query_hash_literal_present (f : ℕ) (hf : f < q.rows.length)
    (term : Fin q.clauses.length × ZMod 3) (ht : term∈q.rows[f])
    (l : SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))
    (hl : l∈Expansion.originalClause source (Fin.cast (congrArg List.length hs) term.1))
    (hlow : q.forward.getD l.variable.val false=false) :
    (l.variable.val,BinaryArithmetic.toNat q.ambient+f)∈
      PackingIncidenceInput.addressedEntries q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward := by
  have hfl : f < q.scopeRows.length := by
    simp only [LeafQueryFrontend.Query.scopeRows,Complete.scopes_length]
    omega
  apply addressed_original_present q.scopeRows q.forward _ _ _ (query_lowOwner q l.variable hlow) hfl
  have he : q.scopeRows[f]=scope (FromTuple.interpretedTerms (clauses:=q.clauses) 1 0 q.codes q.rows[f]) := by
    simp only [LeafQueryFrontend.Query.scopeRows,Complete.scopes]
    rw [List.getElem_append_left (by simpa using hf),List.getElem_map]
  rw [he]
  exact literal_mem_raw_scope q.clauses q.codes source hs hv.2.2.1 _ term ht l hl

include hv in
theorem query_marked_literal_present (i : Fin q.clauses.length) (hm : q.mark=some i)
    (l : SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))
    (hl : l∈Expansion.originalClause source (Fin.cast (congrArg List.length hs) i))
    (hlow : q.forward.getD l.variable.val false=false) :
    (l.variable.val,BinaryArithmetic.toNat q.ambient+q.rows.length)∈
      PackingIncidenceInput.addressedEntries q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward := by
  have hfl : q.rows.length < q.scopeRows.length := by
    simp only [LeafQueryFrontend.Query.scopeRows,Complete.scopes_length,hm,Option.isSome_some,Bool.toNat_true]
    omega
  apply addressed_original_present q.scopeRows q.forward _ _ _ (query_lowOwner q l.variable hlow) hfl
  have he : q.scopeRows[q.rows.length]=Marked.markedScope (q.codes i) := by
    simp only [LeafQueryFrontend.Query.scopeRows,Complete.scopes,hm,Option.toList_some,List.map_cons,List.map_nil]
    rw [List.getElem_append_right (by simp)]
    simp
  rw [he]
  exact literal_mem_marked_scope q.clauses q.codes source hs hv.2.2.1 i l hl

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
