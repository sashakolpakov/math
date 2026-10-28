import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryResources
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashReturnBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryAccepted

/-! The actual normalizer, trial source stage and marked-record parser supply
the literal query sources. These proofs impose no length cap on the suspended
reference tail or mass accumulator, and execute no extra marker stage. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry

open BitProgram StructuredCalls SqrtLog
open HighFrontendSources HashGreedyCode

abbrev Data := State 40 896

def recordState (a : Data) (tail bits : List Bool) : Data :=
  RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse

noncomputable def trialRows {n B : ℕ} (F : DisjointReuse.RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (word : List Bool) : HashScopeProgram.RawTable.Rows F.length :=
  (HashGreedyCandidate.candidate F.length (SparseCode.distanceDenom F.length B)
      (CounterPrograms.value word) ::
    HashGreedyCNF.history (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds).map (raw F.length hm)

noncomputable def trialQuery {n B : ℕ} (F : DisjointReuse.RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (word : List Bool) (e : Fin F.length) (d : Data) : LeafQueryFrontend.Query :=
  rawQueryFromRows F (trialRows F hm shifts Q rounds word) (some e)
    (Encoding.encodeNat e.val) (d.stacks 783) (d.stacks 782) (d.stacks 785)

/-- All source-side obligations at the actual marked callback entry. The
frontend itself owns the single paid marker operation. -/
structure MarkedEntry (q : LeafQueryFrontend.Query) (staged a : Data) : Prop where
  valid : q.Valid
  sources : LeafProgram.Query.Sources q (HighMarkedFrontend.project a)
  clean : LeafProgram.Query.CleanWork (HighMarkedFrontend.project a)
  marked : q.mark.isSome = true
  index : a.stacks 321 = q.index.reverse
  index_empty : a.stacks 705 = []
  flag_empty : a.stacks 706 = []
  scratch : a.stacks 767 = []
  collector : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a
  frontend : q.Ready (LeafProgram.Query.markedInput (HighMarkedFrontend.project a))

theorem record_ready (staged a : Data) (tail bits : List Bool)
    (h : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a) :
    HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged)
      (recordState a tail bits) := by
  refine ⟨(HashMassAdapter.workspace_recordState a false true false tail bits.reverse).trans
    h.workspace_ready, ?_, ?_⟩
  · simpa [recordState, RecordPrograms.state, HashMassAdapter.recordPorts] using h.result_empty
  · simpa [recordState, RecordPrograms.state, HashMassAdapter.recordPorts] using h.scratch_empty

/-- The actual counter word is normalized once, and its physical prefix plus
the attained history is exactly the raw-row table supplied to the frontend. -/
theorem trial_entry {n B : ℕ} (F : DisjointReuse.RawCNF n) (hn : 0 < n)
    (hm : 0 < F.length) (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B) (rounds : ℕ) (word : List Bool)
    (d a : Data) (e : Fin F.length) (tail : List Bool)
    (hword : word.length = HashCandidates.payloadWidth F.length
      (SparseCode.distanceDenom F.length B))
    (hformula : d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hhistory : d.stacks 777 = HashGreedyProgram.encodedHistory
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))
    (hwidth : (d.stacks 783).length = HashCandidates.digitWidth F.length)
    (hmodulus : BinaryArithmetic.toNat (d.stacks 782) = F.length)
    (hambient : BinaryArithmetic.toNat (d.stacks 785) = n)
    (hclean : LeafProgram.Query.CleanWork (HighMarkedFrontend.project d))
    (hscratch : d.stacks 767 = [])
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
        (SparseCode.distanceDenom F.length B) word))) a) :
    MarkedEntry (trialQuery F hm shifts Q rounds word e d)
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
        (SparseCode.distanceDenom F.length B) word))
      (recordState a tail (Encoding.encodeNat e.val)) := by
  let candidateState := HashGreedyExecution.trialState d F.length
    (SparseCode.distanceDenom F.length B) word
  let staged := LeafOuterNative.trialStaged candidateState
  let q := trialQuery F hm shifts Q rounds word e d
  have hc : LeafProgram.Query.CleanWork (HighMarkedFrontend.project candidateState) := by
    intro i hi h321
    have hne : HighMarkedFrontend.stackMap i ≠ 768 := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = 768 at hv
      omega
    simpa only [candidateState, HighMarkedFrontend.project, projectState,
      HashGreedyExecution.trialState, Function.comp_apply, Function.update_of_ne hne] using hclean i hi h321
  have ht : candidateState.stacks 767 = [] := by
    simpa [candidateState, HashGreedyExecution.trialState] using hscratch
  have hs : LeafProgram.Query.Sources q (HighMarkedFrontend.project staged) := by
    apply rawQueryFromRows_trial_sources F (trialRows F hm shifts Q rounds word)
      (some e) (Encoding.encodeNat e.val) (d.stacks 783) (d.stacks 782) (d.stacks 785)
      candidateState
    · simpa [candidateState, HashGreedyExecution.trialState] using hformula
    · simpa only [candidateState, HashGreedyExecution.trialState, Function.update_self,
        Function.update_of_ne (by decide : (777 : Fin 896) ≠ 768), hhistory,
        hwidth, trialRows] using
        supplied_trial_word_raw_encoding (NativeLeafSemantics.indexed F) hm shifts Q rounds word hword
    · simp [candidateState, HashGreedyExecution.trialState]
    · simp [candidateState, HashGreedyExecution.trialState]
    · simp [candidateState, HashGreedyExecution.trialState]
  have hrec := record_ready staged a tail (Encoding.encodeNat e.val) hready
  have hsrc := workspace_sources q staged (recordState a tail (Encoding.encodeNat e.val))
    hs hrec.workspace_ready
  have hcl := workspace_clean staged (recordState a tail (Encoding.encodeNat e.val))
    (trial_clean candidateState hc) hrec.workspace_ready hrec.scratch_empty
  have hmark : q.mark.isSome = true := by
    simp [q, trialQuery, rawQueryFromRows, rawQuery, recordMark]
  have hi : (recordState a tail (Encoding.encodeNat e.val)).stacks 321 = q.index.reverse := by
    simp [recordState, RecordPrograms.state, HashMassAdapter.recordPorts,
      q, trialQuery, rawQueryFromRows, rawQuery]
  refine ⟨?_, hsrc, hcl, hmark, hi, hcl 705 (by decide) (by decide),
    hcl 706 (by decide) (by decide), ?_, hrec, ?_⟩
  · apply rawQueryFromRows_valid F _ (some e) (Encoding.encodeNat e.val)
      (d.stacks 783) (d.stacks 782) (d.stacks 785) hn
    · rw [hwidth]
      exact DyadicWidth.width_pos _
    · rw [hwidth]
      exact HashCandidates.digitWidth_sufficient _
    · intro i he
      cases Option.some.inj he
      rfl
    · exact hmodulus
    · exact hambient
  · exact HashReturnBounds.staged_record_entry_scratch candidateState a hready ht
      tail (Encoding.encodeNat e.val)
  · exact LeafProgram.Query.marked_ready q _ hcl hsrc hmark hi

/-- Preparation supplies the actual low-bank blanks and canonical master
words. The six mutable selector ports are exactly those allowed by the
staged-rounds callback; no global retained-word size premise is needed. -/
theorem prepared_trial_entry {n B : ℕ} (F : DisjointReuse.RawCNF n) (hn : 0 < n)
    (hm : 0 < F.length) (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B) (rounds : ℕ) (word : List Bool)
    (base d a : Data) (e : Fin F.length) (tail : List Bool)
    (hbase : NativeLeafPreparation.Ready n F.length B (initial shifts Q) base)
    (hformula : base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hambient : BinaryArithmetic.toNat (base.stacks 785) = n)
    (hword : word.length = HashCandidates.payloadWidth F.length
      (SparseCode.distanceDenom F.length B))
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hhistory : d.stacks 777 = HashGreedyProgram.encodedHistory
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
        (SparseCode.distanceDenom F.length B) word))) a) :
    MarkedEntry (trialQuery F hm shifts Q rounds word e d)
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
        (SparseCode.distanceDenom F.length B) word))
      (recordState a tail (Encoding.encodeNat e.val)) := by
  have hlo : ∀ i : Fin 896, i.val < 768 → d.stacks i = [] := by
    intro i hi
    have hne (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
      intro he
      subst j
      omega
    rw [hframe i (hne 770 (by decide)) (hne 771 (by decide)) (hne 777 (by decide))
      (hne 778 (by decide)) (hne 779 (by decide)) (hne 781 (by decide))]
    exact NativeCodeAssembly.worker_empty base hbase.worker i hi
  refine trial_entry F hn hm shifts Q rounds word d a e tail hword ?_ hhistory ?_ ?_ ?_ ?_ ?_ hready
  · exact (hframe 784 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hformula
  · rw [hframe 783 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hbase.width]
    exact hbase.modulus_length
  · rw [hframe 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hbase.clauses
  · rw [hframe 785 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hambient
  · intro i _ _
    exact hlo (HighMarkedFrontend.stackMap i) i.isLt
  · exact hlo 767 (by decide)

/-- One cutoff is fixed before all leaf inputs, attained histories, losing
candidates and marked clauses. It applies to the literal query assembled by
`trial_entry`, with no layout or evaluator premise. -/
theorem trial_guard_cutoff (k qi : ℕ) :
    ∃ N : ℕ, ∀ (n B : ℕ) (F : DisjointReuse.RawCNF n)
      (_hv : DisjointReuse.SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      N ≤ n → 0 < n → 0 < B → F.length ≤ n * B → B ≤ Asymptotic.L n ^ qi →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (word : List Bool) (e : Fin F.length) (d : Data),
      BinaryArithmetic.toNat (d.stacks 782) = F.length →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      LeafParametersProgram.Guard ((trialQuery F hm shifts Q rounds word e d).input k) := by
  obtain ⟨N,hN⟩ := HashQueryResources.trial_guard_cutoff k qi
  refine ⟨N, ?_⟩
  intro n B F hv hm hn hnpos hB hmb hpoly shifts Q rounds hr word e d hmod hamb
  exact hN n B F hv hm hn hnpos hB hmb hpoly shifts Q rounds (CounterPrograms.value word) hr
    (some e) (Encoding.encodeNat e.val) (d.stacks 783) (d.stacks 782) (d.stacks 785) hmod hamb

/-- The final query receives precisely the attained history, with no trial
candidate and no marked clause. Its false index is written by `noMarkInput`. -/
noncomputable def acceptedQuery {n B : ℕ} (F : DisjointReuse.RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (d : Data) : LeafQueryFrontend.Query :=
  rawQueryFromRows F
    ((HashGreedyCNF.history (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds).map (raw F.length hm))
    none [false] (d.stacks 783) (d.stacks 782) (d.stacks 785)

structure AcceptedEntry (q : LeafQueryFrontend.Query) (a : Data) : Prop where
  valid : q.Valid
  sources : LeafProgram.Query.Sources q (HighMarkedFrontend.project a)
  clean : LeafProgram.Query.CleanWork (HighMarkedFrontend.project a)
  unmarked : q.mark = none
  index : q.index = [false]
  index_empty : a.stacks 705 = []
  flag_empty : a.stacks 706 = []
  scratch : a.stacks 767 = []
  frontend : q.Ready (LeafProgram.Query.unmarkedInput (HighMarkedFrontend.project a))

/-- The real paid accepted stage supplies the history-only source table and
clears its routing scratch. No second unmarked-input stage is introduced. -/
theorem accepted_entry {n B : ℕ} (F : DisjointReuse.RawCNF n) (hn : 0 < n)
    (hm : 0 < F.length) (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B) (rounds : ℕ) (d : Data)
    (hformula : d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hhistory : d.stacks 777 = HashGreedyProgram.encodedHistory
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))
    (hwidth : (d.stacks 783).length = HashCandidates.digitWidth F.length)
    (hmodulus : BinaryArithmetic.toNat (d.stacks 782) = F.length)
    (hambient : BinaryArithmetic.toNat (d.stacks 785) = n)
    (hclean : LeafProgram.Query.CleanWork (HighMarkedFrontend.project d)) :
    AcceptedEntry (acceptedQuery F hm shifts Q rounds d) (AcceptedQueryStage.staged d) := by
  let q := acceptedQuery F hm shifts Q rounds d
  have hs : LeafProgram.Query.Sources q (HighMarkedFrontend.project (AcceptedQueryStage.staged d)) := by
    apply rawQueryFromRows_accepted_sources F _ none [false]
      (d.stacks 783) (d.stacks 782) (d.stacks 785) d hformula _ rfl rfl rfl
    rw [hhistory, hwidth]
    exact supplied_history_raw_encoding (NativeLeafSemantics.indexed F) hm shifts Q rounds
  have hc := accepted_clean d hclean
  have hm' : q.mark = none := by
    simp [q, acceptedQuery, rawQueryFromRows, rawQuery, recordMark]
  have hi : q.index = [false] := rfl
  refine ⟨?_, hs, hc, hm', hi, hc 705 (by decide) (by decide),
    hc 706 (by decide) (by decide), AcceptedQueryStage.staged_temporary d, ?_⟩
  · apply rawQueryFromRows_valid F _ none [false]
      (d.stacks 783) (d.stacks 782) (d.stacks 785) hn
    · rw [hwidth]
      exact DyadicWidth.width_pos _
    · rw [hwidth]
      exact HashCandidates.digitWidth_sufficient _
    · intro i he
      cases he
    · exact hmodulus
    · exact hambient
  · exact LeafProgram.Query.accepted_ready q _ hc hs hm' hi

/-- The actual completed greedy `RowBoundary` restores preparation's master
words and all lower blank workspace before the history-only count stage. -/
theorem prepared_accepted_entry {n B : ℕ} (F : DisjointReuse.RawCNF n) (hn : 0 < n)
    (hm : 0 < F.length) (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B) (rounds : ℕ) (base d : Data)
    (hbase : NativeLeafPreparation.Ready n F.length B (initial shifts Q) base)
    (hformula : base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hambient : BinaryArithmetic.toNat (base.stacks 785) = n)
    (hboundary : HashGreedyRound.RowBoundary base
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d) :
    AcceptedEntry (acceptedQuery F hm shifts Q rounds d) (AcceptedQueryStage.staged d) := by
  refine accepted_entry F hn hm shifts Q rounds d ?_ hboundary.history ?_ ?_ ?_ ?_
  · exact (hboundary.frame 784 (by decide) (by decide)).trans hformula
  · rw [hboundary.frame 783 (by decide) (by decide), hbase.width]
    exact hbase.modulus_length
  · rw [hboundary.frame 782 (by decide) (by decide)]
    exact hbase.clauses
  · rw [hboundary.frame 785 (by decide) (by decide)]
    exact hambient
  · intro i _ _
    change d.stacks (HighMarkedFrontend.stackMap i) = []
    have hne (j : Fin 896) (hj : 768 ≤ j.val) : HighMarkedFrontend.stackMap i ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = j.val at hv
      omega
    rw [hboundary.frame _ (hne 777 (by decide)) (hne 781 (by decide))]
    exact NativeCodeAssembly.worker_empty base hbase.worker _ i.isLt

/-- The history-only final count passes its actual guard after one cutoff
fixed before all inputs and attained histories. -/
theorem accepted_guard_cutoff (k qi : ℕ) :
    ∃ N : ℕ, ∀ (n B : ℕ) (F : DisjointReuse.RawCNF n)
      (_hv : DisjointReuse.SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      N ≤ n → 0 < n → 0 < B → F.length ≤ n * B → B ≤ Asymptotic.L n ^ qi →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ d : Data, BinaryArithmetic.toNat (d.stacks 782) = F.length →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      LeafParametersProgram.Guard ((acceptedQuery F hm shifts Q rounds d).input k) := by
  obtain ⟨N,hN⟩ := HashQueryResources.history_guard_cutoff k qi
  refine ⟨N, ?_⟩
  intro n B F hv hm hn hnpos hB hmb hpoly shifts Q rounds hr d hmod hamb
  exact hN n B F hv hm hn hnpos hB hmb hpoly shifts Q rounds hr
    none [false] (d.stacks 783) (d.stacks 782) (d.stacks 785) hmod hamb

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
