import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedCleanup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInput
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendHighRun

/-! Typed source and empty-workspace relations follow from the actual trial
and accepted source stages. Changing the marked clause does not change the
immutable source words; its scope and high mask are recomputed by the frontend. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open HighMarkedFrontend

private theorem cast_ne {i j : Fin 768} (h : i ≠ j) : stackMap i ≠ stackMap j :=
  fun he => h (Fin.castAdd_injective 768 128 he)

private theorem unprotected_ne (i : Fin 768) (hi : ¬LeafProgram.Query.Protected i)
    (j : Fin 768) (hj : LeafProgram.Query.Protected j) : i ≠ j := by
  intro h
  subst i
  exact hi hj

private theorem outside_staged (i : Fin 768) (hi : ¬LeafProgram.Query.Protected i)
    (h702 : i ≠ 702) : stackMap i ∉ HashMassStaged.stagedPorts := by
  simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨cast_ne (unprotected_ne i hi 700 (by decide)),
    cast_ne (unprotected_ne i hi 701 (by decide)), cast_ne h702,
    cast_ne (unprotected_ne i hi 707 (by decide)),
    cast_ne (unprotected_ne i hi 708 (by decide)),
    cast_ne (unprotected_ne i hi 709 (by decide))⟩

/-- The physical candidate prefix and copied history are typed as this
query's rows; no scope, layout, or evaluated query is supplied here. -/
theorem trial_sources (q : LeafQueryFrontend.Query) (a : HighMarkedFrontend.Data)
    (hf : a.stacks 784 = Encoding.encodeList id q.clauses)
    (hr : true :: (Encoding.frame (a.stacks 768).reverse ++ a.stacks 777) =
      HashScopeProgram.RawTable.inputBits q.width.length q.rows)
    (hm : a.stacks 782 = q.modulus) (hw : a.stacks 783 = q.width)
    (hn : a.stacks 785 = q.ambient) :
    LeafProgram.Query.Sources q (project (LeafOuterNative.trialStaged a)) := by
  obtain ⟨h0,h1,h7,h8,h9⟩ := LeafOuterNative.trialStaged_sources a
  exact ⟨h0.trans hf,h1.trans hr,h7.trans hm,h8.trans hw,h9.trans hn⟩

/-- The accepted stage uses the saved history literally, with no candidate
prefix and no replacement of the declared ambient count. -/
theorem accepted_sources (q : LeafQueryFrontend.Query) (a : HighMarkedFrontend.Data)
    (hf : a.stacks 784 = Encoding.encodeList id q.clauses)
    (hr : a.stacks 777 = HashScopeProgram.RawTable.inputBits q.width.length q.rows)
    (hm : a.stacks 782 = q.modulus) (hw : a.stacks 783 = q.width)
    (hn : a.stacks 785 = q.ambient) :
    LeafProgram.Query.Sources q (project (AcceptedQueryStage.staged a)) := by
  obtain ⟨h0,h1,h7,h8,h9⟩ := AcceptedQueryStage.staged_sources a
  exact ⟨h0.trans hf,h1.trans hr,h7.trans hm,h8.trans hw,h9.trans hn⟩

theorem trial_clean (a : HighMarkedFrontend.Data)
    (hc : LeafProgram.Query.CleanWork (project a)) :
    LeafProgram.Query.CleanWork (project (LeafOuterNative.trialStaged a)) := by
  intro i hi h321
  change (LeafOuterNative.trialStaged a).stacks (stackMap i) = []
  by_cases h702 : i = 702
  · subst i
    exact LeafOuterNative.prefixed_scratch (LeafOuterNative.finalStaged a)
  rw [HashMassStaged.staged_frame a _ (outside_staged i hi h702)]
  exact hc i hi h321

theorem accepted_clean (a : HighMarkedFrontend.Data)
    (hc : LeafProgram.Query.CleanWork (project a)) :
    LeafProgram.Query.CleanWork (project (AcceptedQueryStage.staged a)) := by
  intro i hi h321
  change (AcceptedQueryStage.staged a).stacks (stackMap i) = []
  by_cases h702 : i = 702
  · subst i
    exact (AcceptedQueryStage.staged_702 a).trans (hc 702 (by decide) (by decide))
  have ht : stackMap i ≠ 767 := cast_ne (unprotected_ne i hi 767 (by decide))
  rw [AcceptedQueryStage.staged_frame a _ (outside_staged i hi h702) ht]
  exact hc i hi h321

/-- Mark selection changes query semantics and hence its newly computed high
set, but leaves the five immutable source words unchanged. -/
theorem sources_with_mark (q : LeafQueryFrontend.Query) (a : HighMarkedFrontend.Data)
    (h : LeafProgram.Query.Sources q (project a))
    (mark : Option (Fin q.clauses.length)) (index : List Bool) :
    LeafProgram.Query.Sources { q with mark := mark, index := index } (project a) :=
  ⟨h.formula,h.rows,h.modulus,h.width,h.ambient⟩

/-- The actual collector's workspace equality preserves the source words at
every marked callback boundary. -/
theorem workspace_sources (q : LeafQueryFrontend.Query) (a b : HighMarkedFrontend.Data)
    (hs : LeafProgram.Query.Sources q (project a))
    (h : HashMassAdapter.workspace b = HashMassAdapter.workspace a) :
    LeafProgram.Query.Sources q (project b) := by
  constructor
  · exact (HashMassAdapter.workspace_frame a b h 700 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.formula
  · exact (HashMassAdapter.workspace_frame a b h 701 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.rows
  · exact (HashMassAdapter.workspace_frame a b h 707 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.modulus
  · exact (HashMassAdapter.workspace_frame a b h 708 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.width
  · exact (HashMassAdapter.workspace_frame a b h 709 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.ambient

theorem workspace_clean (a b : HighMarkedFrontend.Data)
    (hc : LeafProgram.Query.CleanWork (project a))
    (h : HashMassAdapter.workspace b = HashMassAdapter.workspace a)
    (h324 : b.stacks 324 = []) : LeafProgram.Query.CleanWork (project b) := by
  intro i hi h321
  change b.stacks (stackMap i) = []
  by_cases he : i = 324
  · subst i
    exact h324
  rw [HashMassAdapter.workspace_frame a b h (stackMap i)
    (cast_ne (unprotected_ne i hi 320 (by decide))) (cast_ne h321)
    (cast_ne (unprotected_ne i hi 322 (by decide)))
    (cast_ne (unprotected_ne i hi 323 (by decide))) (cast_ne he)]
  exact hc i hi h321

/-- Every current hashed or marked scope comes from an actual source literal.
This applies uniformly to the optional mark; no precomputed scope bound is an
input to the machine. -/
theorem scopeRows_lt (q : LeafQueryFrontend.Query) (n : ℕ)
    (hc : ∀ i, ∀ c ∈ q.codes i, c < 2*n) :
    ∀ row ∈ q.scopeRows, ∀ v ∈ row, v < n := by
  intro row hr v hv
  change row ∈ (q.rows.map (fun terms => HashScopeProgram.scope
    (HashScopeProgram.FromTuple.interpretedTerms (clauses := q.clauses) 1 0 q.codes terms)) ++
      q.mark.toList.map (fun i => HashScopeProgram.Marked.markedScope (q.codes i))) at hr
  rcases List.mem_append.mp hr with hh | hm
  · obtain ⟨terms,_ht,rfl⟩ := List.mem_map.mp hh
    obtain ⟨term,_hm,c,hc',rfl⟩ :=
      (HashScopeProgram.FromTuple.mem_interpreted_scope 1 0 q.codes terms v).mp hv
    exact (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
      (by simpa only [Nat.mul_comm] using hc term.1 c hc')
  · obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hm
    obtain ⟨c,hc',he⟩ := (SubexpScopeProducer.mem_scope [true] (q.codes i) v).mp hv
    have he' : c/2=v := by simpa [BinaryArithmetic.toNat,BinaryArithmetic.bitVal] using he
    rw [← he']
    exact (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
      (by simpa only [Nat.mul_comm] using hc i c hc')

/-- A proof-side description of precisely the native raw records and source
words. The runtime receives the existing encoded masters, not this record. -/
def rawQuery {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool) : LeafQueryFrontend.Query where
  clauses := NativeTerminal.clauseRecords F
  codes := NativeLeafSemantics.recordCodes F
  rows := rows
  mark := mark
  index := index
  width := width
  modulus := modulus
  ambient := ambient

theorem rawQuery_clauses {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool) :
    ∀ i, (rawQuery F rows mark index width modulus ambient).clauses[i.val]=
      Encoding.encodeList Encoding.encodeNat
        ((rawQuery F rows mark index width modulus ambient).codes i) :=
  NativeLeafSemantics.recordCodes_word F

theorem rawQuery_scopeRows {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool) (hn : BinaryArithmetic.toNat ambient=n) :
    ∀ row ∈ (rawQuery F rows mark index width modulus ambient).scopeRows,
      ∀ v ∈ row, v < BinaryArithmetic.toNat ambient := by
  rw [hn]
  exact scopeRows_lt _ n (NativeLeafSemantics.recordCodes_lt F)

/-- The semantic dependent cast retains every physically encoded row word.
It changes no clause index value and introduces no runtime row traversal. -/
def castRows {m m' : ℕ} (h : m=m') (rows : HashScopeProgram.RawTable.Rows m) :
    HashScopeProgram.RawTable.Rows m' :=
  rows.map (List.map (fun term => (Fin.cast h term.1,term.2)))

theorem inputBits_cast {m m' : ℕ} (h : m=m') (rows : HashScopeProgram.RawTable.Rows m)
    (width : ℕ) : HashScopeProgram.RawTable.inputBits width (castRows h rows)=
      HashScopeProgram.RawTable.inputBits width rows := by
  subst m'
  simp [castRows]

theorem recordLength {n : ℕ} (F : DisjointReuse.RawCNF n) :
    F.length=(NativeTerminal.clauseRecords F).length := by simp [NativeTerminal.clauseRecords]

def recordRows {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) := castRows (recordLength F) rows

def recordMark {n : ℕ} (F : DisjointReuse.RawCNF n) (mark : Option (Fin F.length)) :=
  mark.map (Fin.cast (recordLength F))

/-- Actual selected rows and marked indices keep their literal numeric bytes
when related to the serialized clause-record indexing. -/
def rawQueryFromRows {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool) : LeafQueryFrontend.Query :=
  rawQuery F (recordRows F rows) (recordMark F mark) index width modulus ambient

theorem recordRows_input {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (width : ℕ) :
    HashScopeProgram.RawTable.inputBits width (recordRows F rows)=
      HashScopeProgram.RawTable.inputBits width rows := inputBits_cast _ _ _

theorem recordMark_index {n : ℕ} (F : DisjointReuse.RawCNF n)
    (mark : Option (Fin F.length)) (index : List Bool)
    (hi : ∀ i, mark=some i → index=Encoding.encodeNat i.val) :
    ∀ i, recordMark F mark=some i → index=Encoding.encodeNat i.val := by
  intro i h
  obtain ⟨j,hj,hji⟩ := Option.map_eq_some_iff.mp h
  subst i
  exact hi j hj

theorem rawQueryFromRows_trial_sources {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool) (a : HighMarkedFrontend.Data)
    (hf : a.stacks 784=Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hr : true :: (Encoding.frame (a.stacks 768).reverse ++ a.stacks 777)=
      HashScopeProgram.RawTable.inputBits width.length rows)
    (hm : a.stacks 782=modulus) (hw : a.stacks 783=width) (hn : a.stacks 785=ambient) :
    LeafProgram.Query.Sources (rawQueryFromRows F rows mark index width modulus ambient)
      (project (LeafOuterNative.trialStaged a)) := by
  apply trial_sources _ a hf _ hm hw hn
  exact hr.trans (recordRows_input F rows width.length).symm

theorem rawQueryFromRows_accepted_sources {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool) (a : HighMarkedFrontend.Data)
    (hf : a.stacks 784=Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hr : a.stacks 777=HashScopeProgram.RawTable.inputBits width.length rows)
    (hm : a.stacks 782=modulus) (hw : a.stacks 783=width) (hn : a.stacks 785=ambient) :
    LeafProgram.Query.Sources (rawQueryFromRows F rows mark index width modulus ambient)
      (project (AcceptedQueryStage.staged a)) := by
  apply accepted_sources _ a hf _ hm hw hn
  exact hr.trans (recordRows_input F rows width.length).symm

/-- Concrete raw records satisfy every source-side frontend validity field.
The positive ambient case is selected by the actual terminal dispatcher. -/
theorem rawQuery_valid {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool)
    (hn : 0<n) (hw : 0<width.length) (hsize : 3*F.length≤2^width.length)
    (hi : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hm : BinaryArithmetic.toNat modulus=F.length)
    (ha : BinaryArithmetic.toNat ambient=n) :
    (rawQuery F rows mark index width modulus ambient).Valid := by
  refine ⟨hw,?_,rawQuery_clauses F rows mark index width modulus ambient,
    ?_,hi,?_,rawQuery_scopeRows F rows mark index width modulus ambient ha⟩
  · simpa only [rawQuery,ha] using hn
  · simpa only [rawQuery,NativeTerminal.clauseRecords,List.length_map] using hsize
  · simpa only [rawQuery,NativeTerminal.clauseRecords,List.length_map] using hm

theorem rawQueryFromRows_valid {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool)
    (hn : 0<n) (hw : 0<width.length) (hsize : 3*F.length≤2^width.length)
    (hi : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hm : BinaryArithmetic.toNat modulus=F.length)
    (ha : BinaryArithmetic.toNat ambient=n) :
    (rawQueryFromRows F rows mark index width modulus ambient).Valid :=
  rawQuery_valid F _ _ index width modulus ambient hn hw hsize
    (recordMark_index F mark index hi) hm ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources
