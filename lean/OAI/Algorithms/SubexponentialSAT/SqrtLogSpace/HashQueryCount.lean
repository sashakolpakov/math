import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryCountCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSpecTarget

/-! The actual query's ternary count is the selector's exact natural score.
Literal source occurrences and the entire ambient assignment type are retained. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryCount

open SqrtLog DisjointReuse HighFrontendSources HashGreedyCode HashQueryEntry
open LeafProgram OuterQuery.Count

/-- Native clause records are the original interpreter's literal source bytes. -/
theorem clauseRecords_eq {n : ℕ} (F : RawCNF n) :
    NativeTerminal.clauseRecords F = HashInputProgram.Expansion.encodedClauses F := by
  apply List.map_congr_left
  intro clause _
  rw [HashInputProgram.clausePayload_codes]
  simp only [ExecSparsifyEncoding.encodeList_map]
  rfl

/-- The dependent record-index cast preserves every raw term and literal. -/
theorem rawHashes_recordRows {n : ℕ} (F : RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) :
    rawHashes (fun i => F.get (NativeLeafSemantics.recordIndex F i)) (recordRows F rows) =
      rawHashes F.get rows := by
  simp [rawHashes, recordRows, castRows, List.map_map, Function.comp_def,
    NativeLeafSemantics.recordIndex, List.get_eq_getElem]

/-- Decoding changes only the row representation, not the marked natural count. -/
theorem payload_marked_count {n : ℕ} (F : RawCNF n) (hm : 0 < F.length)
    (payloads : List (List Bool)) (e : Fin F.length) :
    PreparedBranchCount.fullCount (rawHashes F.get (payloads.map (raw F.length hm)))
      true (F.get e) =
      markedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F)) payloads
        (fun i x => !(NativeLeafSemantics.indexed F i).eval x) e := by
  rw [fullCount_payload_marked]
  unfold markedCount
  apply Finset.sum_congr rfl
  intro x _
  rw [HashGreedyCNF.accepts_decode]
  rfl

/-- The unmarked count keeps all ambient assignments, including unused bits. -/
theorem payload_accepted_count {n : ℕ} (F : RawCNF n) (hm : 0 < F.length)
    (payloads : List (List Bool)) (clause : List (SAT.Literal (Fin n))) :
    PreparedBranchCount.fullCount (rawHashes F.get (payloads.map (raw F.length hm)))
      false clause =
      HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F)) payloads := by
  rw [fullCount_payload_none]
  unfold HashSelect.acceptedCount
  apply Finset.sum_congr rfl
  intro x _
  rw [HashGreedyCNF.accepts_decode]
  rfl


/-- Equality of ambient dimensions changes no literal bytes. -/
theorem rawQuery_source_bytes {n N : ℕ} (F : RawCNF n) (h : n = N)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool) :
    (rawQueryFromRows F rows mark index width modulus ambient).clauses =
      HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F) := by
  cases h
  exact clauseRecords_eq F

section FactorSource

open SubexpLiftRing MulticolorTypes Subexp.ConstructivePacking LayoutProgram

variable {n N r Q d : ℕ} (F : RawCNF n) (h : n = N)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool)

variable (hv : (rawQueryFromRows F rows mark index width modulus ambient).Valid)
    (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1)) (J : ℕ) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (scalarWidth : List Bool) (hw : scalarWidth.length = baseWidth 3 p.t)
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3 * p.t))

/-- The actual constructor's clause-index casts preserve the full raw hash
list. The ambient cast is equality transport, not variable compression. -/
theorem factorSpec_sourceHashes :
    NodeConcrete.sourceHashes (PreparedSource.factorSpec p ps P
      (rawQueryFromRows F rows mark index width modulus ambient) hv J hJ
      (Eq.mp (congrArg RawCNF h) F)
      (rawQuery_source_bytes F h rows mark index width modulus ambient)
      theta scalarWidth hw code) = h ▸ rawHashes F.get rows := by
  cases h
  simp [NodeConcrete.sourceHashes, PreparedSource.factorSpec, PreparedSource.castRows,
    rawQueryFromRows, rawQuery, recordRows, castRows, rawHashes, List.map_map,
    Function.comp_def, HashInputProgram.Expansion.originalClause, List.get_eq_getElem]

/-- The high-assignment sum counts the exact literal query at the original
ambient dimension. Arithmetic, packing and node data impose no extra filter. -/
theorem factorSpec_fullCount :
    let spec := PreparedSource.factorSpec p ps P
      (rawQueryFromRows F rows mark index width modulus ambient) hv J hJ
      (Eq.mp (congrArg RawCNF h) F)
      (rawQuery_source_bytes F h rows mark index width modulus ambient)
      theta scalarWidth hw code
    PreparedBranchCount.fullCount (NodeConcrete.sourceHashes spec) spec.marked spec.markedClause =
      PreparedBranchCount.fullCount (rawHashes F.get rows) mark.isSome
        (F[(mark.map Fin.val).getD 0]?.getD []) := by
  cases h
  dsimp only
  rw [factorSpec_sourceHashes F rfl rows mark index width modulus ambient hv p ps P J hJ
    theta scalarWidth hw code]
  cases mark <;> rfl

end FactorSource


/-- The exact prepared factor constructor returns the selector count for
both marked and unmarked payloads, at the original ambient dimension. -/
theorem factorSpec_payload_count {n N r Q d : ℕ} (F : RawCNF n) (h : n = N)
    (hm : 0 < F.length) (payloads : List (List Bool)) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool)
    (hv : (rawQueryFromRows F (payloads.map (raw F.length hm)) mark index width modulus ambient).Valid)
    (p : LayoutProgram.SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : Subexp.ConstructivePacking.PackingData (Fin ps.length) (MulticolorTypes.UniversalType r Q 1))
    (J : ℕ) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (SubexpLiftRing.baseWidth 3 p.t) d)
    (scalarWidth : List Bool) (hw : scalarWidth.length = SubexpLiftRing.baseWidth 3 p.t)
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3 * p.t)) :
    let spec := PreparedSource.factorSpec p ps P
      (rawQueryFromRows F (payloads.map (raw F.length hm)) mark index width modulus ambient)
      hv J hJ (Eq.mp (congrArg RawCNF h) F)
      (rawQuery_source_bytes F h _ mark index width modulus ambient) theta scalarWidth hw code
    PreparedBranchCount.fullCount (NodeConcrete.sourceHashes spec) spec.marked spec.markedClause =
      match mark with
      | none => HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F)) payloads
      | some e => markedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F)) payloads
          (fun i x => !(NativeLeafSemantics.indexed F i).eval x) e := by
  dsimp only
  rw [factorSpec_fullCount F h _ mark index width modulus ambient hv p ps P J hJ
    theta scalarWidth hw code]
  cases mark with
  | none => exact payload_accepted_count F hm payloads _
  | some e =>
      simpa [List.get_eq_getElem] using payload_marked_count F hm payloads e

/-- Every trial, including a losing rank, returns the exact marked score of
its normalized candidate followed by the attained history. -/
theorem trial_count {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (word : List Bool) (e : Fin F.length) :
    PreparedBranchCount.fullCount (rawHashes F.get (trialRows F hm shifts Q rounds word))
      true (F.get e) =
      markedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCandidate.candidate F.length (SparseCode.distanceDenom F.length B)
            (CounterPrograms.value word) ::
          HashGreedyCNF.history (NativeLeafSemantics.indexed F)
            (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds)
        (fun i x => !(NativeLeafSemantics.indexed F i).eval x) e :=
  payload_marked_count F hm _ e

/-- The accepted query is the full count of the attained history, with no
current candidate prefix and no marked-clause filter. -/
theorem accepted_count {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (clause : List (SAT.Literal (Fin n))) :
    PreparedBranchCount.fullCount (rawHashes F.get
      ((HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds).map (raw F.length hm)))
      false clause =
      HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) :=
  payload_accepted_count F hm _ clause

/-- The code's actual good/distance facts and completed greedy rounds make
the final unmarked query exactly the original ambient model count. -/
theorem final_count {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
    (clause : List (SAT.Literal (Fin n))) :
    PreparedBranchCount.fullCount (rawHashes F.get
      ((HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q)
        (HashSelect.loopCap n F.length)).map (raw F.length hm))) false clause = rawCount F := by
  rw [accepted_count]
  exact NativeLeafSemantics.history_count F hm hB shifts Q hs hQ

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryCount
