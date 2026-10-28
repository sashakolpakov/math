import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryCount
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryEntryFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds

/-! Literal marked and accepted query continuations for the actual prepared
leaf. Shadow execution preserves unrestricted caller words for time; the
same replay counts those words separately in maximum prefix storage. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries

open BitProgram StructuredCalls SqrtLog DisjointReuse
open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram
open HashGreedyProgram.NativeRound

/-- Equality transport of the ambient dimension preserves the original
literal width bound used by the actual high-query execution. -/
theorem source_width {n N k : ℕ} (F : RawCNF n) (h : n = N)
    (hv : SparseDFSRefinement.Valid k F) :
    ∀ clause ∈ Eq.mp (congrArg RawCNF h) F, clause.length ≤ k := by
  cases h
  exact hv.width

/-- The exact raw expression returned by the actual high iterator is the
same full ambient count as the literal query. Index casts retain every slot. -/
theorem raw_query_fullCount {n N : ℕ} (F : RawCNF n) (h : n = N)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool)
    (hsource : (rawQueryFromRows F rows mark index width modulus ambient).clauses =
      HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F)) :
    PreparedBranchCount.fullCount
      ((PreparedSource.castRows (congrArg List.length hsource)
        (rawQueryFromRows F rows mark index width modulus ambient).rows).map
          (fun terms => terms.map (fun term =>
            (term.2, HashInputProgram.Expansion.originalClause
              (Eq.mp (congrArg RawCNF h) F) term.1))))
      (rawQueryFromRows F rows mark index width modulus ambient).mark.isSome
      ((Eq.mp (congrArg RawCNF h) F)[PreparedSource.markIndex
        (rawQueryFromRows F rows mark index width modulus ambient)]?.getD []) =
      PreparedBranchCount.fullCount (OuterQuery.Count.rawHashes F.get rows) mark.isSome
        (F[(mark.map Fin.val).getD 0]?.getD []) := by
  cases h
  simp [PreparedSource.castRows, rawQueryFromRows, rawQuery, recordRows,
    HighFrontendSources.castRows, recordMark, OuterQuery.Count.rawHashes,
    List.map_map, Function.comp_def, HashInputProgram.Expansion.originalClause,
    List.get_eq_getElem, PreparedSource.markIndex]
  congr 1

/-- Marked and unmarked payloads have exactly the selector accessor count,
using the very same full-count expression produced by the high iterator. -/
theorem raw_query_payload_count {n N : ℕ} (F : RawCNF n) (h : n = N)
    (hm : 0 < F.length) (payloads : List (List Bool)) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool)
    (hsource : (rawQueryFromRows F (payloads.map (raw F.length hm)) mark
      index width modulus ambient).clauses =
      HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F)) :
    PreparedBranchCount.fullCount
      ((PreparedSource.castRows (congrArg List.length hsource)
        (rawQueryFromRows F (payloads.map (raw F.length hm)) mark
          index width modulus ambient).rows).map
          (fun terms => terms.map (fun term =>
            (term.2, HashInputProgram.Expansion.originalClause
              (Eq.mp (congrArg RawCNF h) F) term.1))))
      (rawQueryFromRows F (payloads.map (raw F.length hm)) mark
        index width modulus ambient).mark.isSome
      ((Eq.mp (congrArg RawCNF h) F)[PreparedSource.markIndex
        (rawQueryFromRows F (payloads.map (raw F.length hm)) mark
          index width modulus ambient)]?.getD []) =
      match mark with
      | none => HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F)) payloads
      | some e => markedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F)) payloads
          (fun i x => !(NativeLeafSemantics.indexed F i).eval x) e := by
  rw [raw_query_fullCount F h _ mark index width modulus ambient hsource]
  cases mark with
  | none => exact HashQueryCount.payload_accepted_count F hm payloads _
  | some e =>
      simpa [List.get_eq_getElem] using HashQueryCount.payload_marked_count F hm payloads e

/-- The actual setup prefix cap bounds its seeded endpoint independently of
its duration. No high-loop cost enters this boundary allowance. -/
theorem seeded_bound {q k input command marker budget S B Cp dp timeCap spaceCap}
    (run : NativeHashQuerySetup.SetupRun q k input command marker budget S B Cp dp timeCap spaceCap) :
    ∀ i, ((HighCountSeed.initialized (HighMarkedFrontend.result run.front run.prepared.output)
      run.prepared.seedRegs).stacks i).length ≤ max spaceCap B := by
  intro i
  exact run.space.bound _ _ (Nat.le_refl _)
    (compiled_halt_trace run.eval 778 777) i

/-- The actual scalar producer stores the field cardinality minus two on44.
Its numeric cap therefore bounds the search field cardinality polynomially. -/
theorem field_card_bound (q : LeafQueryFrontend.Query) (k S : ℕ)
    (padding : Fin 8 → ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (hv : ∀ j, (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
      (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤ S) :
    3 ^ ((LeafParametersProgram.Execute.guardedModel (q.input k) padding).val 34) ≤ S + 2 := by
  have h := hv 44
  rw [Query.ring_exponent _ _ hg] at h
  omega

/-- Prepared lower-bank emptiness and the exact six-port caller frame survive
the real candidate-only normalization. No length bound on that caller occurs. -/
theorem trial_workspace {n m B depth : ℕ} {initial : List (List Bool)}
    (base d : State 40 896) (word : List Bool)
    (hr : NativeLeafPreparation.Ready n m B initial base)
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hupper : ∀ i : Fin 896,
      (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) → base.stacks i = []) :
    Query.CleanWork (HighMarkedFrontend.project (HashGreedyExecution.trialState d m depth word)) ∧
    (HashGreedyExecution.trialState d m depth word).stacks 767 = [] ∧
    ∀ i : Fin 896,
      (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
      (HashGreedyExecution.trialState d m depth word).stacks i = [] := by
  have low (i : Fin 896) (hi : i.val < 768) :
      (HashGreedyExecution.trialState d m depth word).stacks i = [] := by
    have hn (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
      intro he; subst j; omega
    rw [show (HashGreedyExecution.trialState d m depth word).stacks i = d.stacks i from
      Function.update_of_ne (hn 768 (by decide)) _ _]
    rw [hframe i (hn 770 (by decide)) (hn 771 (by decide)) (hn 777 (by decide))
      (hn 778 (by decide)) (hn 779 (by decide)) (hn 781 (by decide))]
    exact NativeLeafRun.ready_low hr i hi
  refine ⟨?_, low 767 (by decide), ?_⟩
  · intro i _ _
    exact low (HighMarkedFrontend.stackMap i) i.isLt
  · intro i hi
    have hn (j : Fin 896) (hj : j.val < 788) : i ≠ j := by
      intro he; subst j; omega
    rw [show (HashGreedyExecution.trialState d m depth word).stacks i = d.stacks i from
      Function.update_of_ne (hn 768 (by decide)) _ _]
    rw [hframe i (hn 770 (by decide)) (hn 771 (by decide)) (hn 777 (by decide))
      (hn 778 (by decide)) (hn 779 (by decide)) (hn 781 (by decide))]
    exact hupper i hi

/-- The literal collector entry satisfies the actual complete return's
blank-bank and scratch preconditions, including all upper query banks. -/
theorem marked_entry_blank {n m B depth : ℕ} {initial : List (List Bool)}
    (base d a : State 40 896) (word tail bits : List Bool)
    (hr : NativeLeafPreparation.Ready n m B initial base)
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hupper : ∀ i : Fin 896,
      (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) → base.stacks i = [])
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d m depth word))) a) :
    (∀ i, HashMarkedReturn.kept i = false → (i.val < 320 ∨ 324 < i.val) →
      (recordState a tail bits).stacks i = []) ∧ (recordState a tail bits).stacks 767 = [] := by
  obtain ⟨hlow, htmp, hup⟩ := trial_workspace base d word hr hframe hupper
  exact ⟨HashReturnBounds.staged_record_entry_blank _ a hlow hup hready tail bits,
    HashReturnBounds.staged_record_entry_scratch _ a hready htmp tail bits⟩


open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources

/-- This is the literal full-count expression returned by the fixed native
high iterator. Its source uses the unchanged ambient dimension. -/
noncomputable def literalCount (q : LeafQueryFrontend.Query)
    (source : RawCNF (BinaryArithmetic.toNat q.ambient))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source) : ℕ :=
  PreparedBranchCount.fullCount
    ((PreparedSource.castRows (congrArg List.length hsource) q.rows).map
      (fun terms => terms.map (fun term =>
        (term.2, HashInputProgram.Expansion.originalClause source term.1))))
    q.mark.isSome (source.getD (PreparedSource.markIndex q) [])


/-- The high iterator's natural count never exceeds all assignments of the
unchanged ambient dimension. This gives the complete count word's width. -/
theorem literalCount_le (q : LeafQueryFrontend.Query)
    (source : RawCNF (BinaryArithmetic.toNat q.ambient))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source) :
    literalCount q source hsource ≤ 2^(BinaryArithmetic.toNat q.ambient) :=
  HighQueryLoop.full_count_le _ _ _

/-- Literal trial byte decoding is exactly the normalized candidate and
attained history accessor, including every losing candidate. -/
theorem literal_trial_count {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (word : List Bool) (e : Fin F.length) (d : State 40 896)
    (h : n = BinaryArithmetic.toNat (trialQuery F hm shifts Q rounds word e d).ambient)
    (hsource : (trialQuery F hm shifts Q rounds word e d).clauses =
      HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F)) :
    literalCount (trialQuery F hm shifts Q rounds word e d)
      (Eq.mp (congrArg RawCNF h) F) hsource =
      markedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCandidate.candidate F.length (SparseCode.distanceDenom F.length B)
          (CounterPrograms.value word) :: HashGreedyCNF.history (NativeLeafSemantics.indexed F)
            (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds)
        (fun i x => !(NativeLeafSemantics.indexed F i).eval x) e := by
  exact raw_query_payload_count F h hm _ (some e) (Encoding.encodeNat e.val)
    (d.stacks 783) (d.stacks 782) (d.stacks 785) hsource

/-- Final history-only queries have precisely the selector's accepted
count; no trial row or marked-clause filter remains. -/
theorem literal_accepted_count {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (d : State 40 896)
    (h : n = BinaryArithmetic.toNat (acceptedQuery F hm shifts Q rounds d).ambient)
    (hsource : (acceptedQuery F hm shifts Q rounds d).clauses =
      HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F)) :
    literalCount (acceptedQuery F hm shifts Q rounds d)
      (Eq.mp (congrArg RawCNF h) F) hsource =
      HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) := by
  exact raw_query_payload_count F h hm _ none [false]
    (d.stacks 783) (d.stacks 782) (d.stacks 785) hsource


section Replay

variable {q : LeafQueryFrontend.Query} {k : ℕ} {input : State 40 896}
  {frontBudget S Cp dp timeCap A : ℕ}

local notation "erased" => HighQueryEntryShadow.erase input

/-- Every erased word is counted in the bounded actual shadow input. -/
theorem shadow_input_bound
    {command : Cmd 40 896} {marker : State 40 768}
    (run : NativeHashQuerySetup.SetupRun q k (HighQueryEntryShadow.erase input) command marker frontBudget S 0
      Cp dp timeCap A) : ∀ i, ((erased).stacks i).length ≤ S := by
  intro i
  by_cases hi : i ∈ HighQueryProgram.Carried.words
  · simp [HighQueryEntryShadow.erase, ProgramTapeReplay.rebaseState,
      ProgramTapeReplay.rebaseStacks, hi]
  · exact run.input_visible i hi

variable (run : NativeHashQuerySetup.SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.command k)
  (Query.markedInput (project (HighQueryEntryShadow.erase input))) frontBudget S 0 Cp dp timeCap A)
  (RB RI frontCost frameBound : ℕ) (staged : State 40 896)
  (entry : MarkedEntry q staged input)
  (hindex : q.index = Encoding.encodeNat (PreparedSource.markIndex q))
  (source : RawCNF (BinaryArithmetic.toNat q.ambient))
  (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
  (hwidth : ∀ clause ∈ source, clause.length ≤ k)
  (hvalues : ∀ j,
    (Circuit.result Serialization.code (Execute.guardedModel (q.input k) run.padding)).val j ≤ S ∧
    (Execute.guardedModel (q.input k) run.padding).val j ≤ S)
  (hSA : S ≤ A) (hfront : frontBudget ≤ frontCost)
  (hblank : ∀ i, HashMarkedReturn.kept i = false → (i.val < 320 ∨ 324 < i.val) →
    input.stacks i = [])
  (hhidden : ∀ i, i ∈ HighQueryProgram.Carried.words → (input.stacks i).length ≤ frameBound)

local notation "model" => Execute.guardedModel (q.input k) run.padding
local notation "work" => CostAssembly.assembledWork k (ambient q)
  (ofPacking q k RB 1 1 RI 1 run.guard run.prepared.first run.prepared.rest)
local notation "highCost" => HighQueryCorrect.loopBudget (BinaryArithmetic.toNat q.ambient)
  (Finset.card (highSet q)) (Circuit.Model.val model 33) (Circuit.Model.val model 34) (Circuit.Model.val model 21) (Circuit.Model.val model 42) A (A+S+2) work
local notation "highSpace" => HighQueryCorrect.loopSpace (BinaryArithmetic.toNat q.ambient)
  (Finset.card (highSet q)) (Circuit.Model.val model 33) (Circuit.Model.val model 34) (Circuit.Model.val model 42) A (A+S+2)

include entry hindex hwidth hvalues hSA hfront hblank hhidden in
/-- Actual complete marked execution followed by its same-step opaque-word
replay. The runtime has no suspended-word allowance; all prefixes count it. -/
theorem marked_replay :
    ∃ steps output,
      Eval (HighQueryProgram.marked k) steps input output ∧
      steps+1 ≤ HighQueryCorrect.markedBudget frontCost (S+frontBudget)
        (Cp*(S+frontBudget+1)^dp) highCost (QueryHeadBudgets.compact A) ∧
      output.stacks 323 = countWord (literalCount q source hsource) ∧
      HashMassAdapter.workspace output = HashMassAdapter.workspace input ∧
      HashMassAdapter.read output = HashMassAdapter.read input ∧
      RecordPrograms.state HashMassAdapter.recordPorts output false true false
        (input.stacks 320) [] = output ∧ output.stacks 324 = [] ∧
      StageSpace (HighQueryProgram.marked k) (steps+1) input
        (max (HighQueryCorrect.space q S frontCost (S+frontBudget) 0
          (Cp*(S+frontBudget+1)^dp) highSpace (QueryHeadBudgets.compact A)) frameBound) := by
  have hr := Query.marked_ready q (project erased)
    (HighQueryEntryShadow.cleanWork input entry.clean)
    (HighQueryEntryShadow.sources q input entry.sources) entry.marked
    (HighQueryEntryShadow.reference q input entry.index)
  have hw : ∀ i, ((HighCountSeed.initialized (result run.front run.prepared.output)
      run.prepared.seedRegs).stacks i).length ≤ A := by
    simpa only [Nat.max_zero] using seeded_bound run
  have hqsize : 3^(Circuit.Model.val model 34) ≤ A+S+2 :=
    (field_card_bound q k S run.padding run.guard (fun j => (hvalues j).1)).trans (by omega)
  have hfrontendCost : run.frontendSteps ≤ frontCost := by
    change run.data.frontendSteps ≤ frontCost
    have htime : run.data.frontendSteps + 1 ≤ frontBudget := run.frontend_time
    omega
  obtain ⟨steps,output,he,ht,hcount,hws,_hread,hrecord,h324,hs⟩ :=
    HighQueryCorrect.marked run.prepared RB 1 1 RI 1 entry.valid _ run.words
      run.frontend_state hr hindex source hsource hwidth A (A+S+2) hw
      (fun j => (hvalues j).2.trans hSA) (by omega) hqsize erased
      run.frontendSteps frontCost S run.frontend hfrontendCost
      (shadow_input_bound run) run.kept (HighQueryEntryShadow.marked_discarded input hblank)
      (HighQueryEntryShadow.scratch input entry.scratch)
  have hp : output.regs 16 = false ∧ output.regs 17 = true ∧ output.regs 18 = false := by
    have h16 := congrArg (fun a : State 40 896 => a.regs 16) hrecord
    have h17 := congrArg (fun a : State 40 896 => a.regs 17) hrecord
    have h18 := congrArg (fun a : State 40 896 => a.regs 18) hrecord
    simpa [RecordPrograms.state, HashMassAdapter.recordPorts] using
      And.intro h16.symm (And.intro h17.symm h18.symm)
  have h321 : output.stacks 321 = [] := by
    have h := congrArg (fun a : State 40 896 => a.stacks 321) hrecord
    simpa [RecordPrograms.state, HashMassAdapter.recordPorts] using h.symm
  obtain ⟨her,hwr,hrr,hrec,hcr,hscr,hsr⟩ :=
    HighQueryReturnReplay.marked he hws hp h321 h324 hcount hs hhidden
  exact ⟨steps,_,her,ht,hcr,hwr,hrr,hrec,hscr,hsr⟩

end Replay


section AcceptedReplay

variable {q : LeafQueryFrontend.Query} {k : ℕ} {input : State 40 896}
  {frontBudget S Cp dp timeCap A : ℕ}

local notation "erased" => HighQueryEntryShadow.erase input

variable (run : NativeHashQuerySetup.SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.acceptedCommand k)
  (Query.unmarkedInput (project (HighQueryEntryShadow.erase input))) frontBudget S 0 Cp dp timeCap A)
  (RB RI frontCost frameBound : ℕ)
  (entry : AcceptedEntry q input)
  (hindex : q.index = Encoding.encodeNat (PreparedSource.markIndex q))
  (source : RawCNF (BinaryArithmetic.toNat q.ambient))
  (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
  (hwidth : ∀ clause ∈ source, clause.length ≤ k)
  (hvalues : ∀ j,
    (Circuit.result Serialization.code (Execute.guardedModel (q.input k) run.padding)).val j ≤ S ∧
    (Execute.guardedModel (q.input k) run.padding).val j ≤ S)
  (hSA : S ≤ A) (hfront : frontBudget ≤ frontCost)
  (hblank : ∀ i, i ≠ 788 → HashMarkedReturn.kept i = false → input.stacks i = [])
  (hhidden : ∀ i, i ∈ HighQueryProgram.Carried.words → (input.stacks i).length ≤ frameBound)

local notation "model" => Execute.guardedModel (q.input k) run.padding
local notation "work" => CostAssembly.assembledWork k (ambient q)
  (ofPacking q k RB 1 1 RI 1 run.guard run.prepared.first run.prepared.rest)
local notation "highCost" => HighQueryCorrect.loopBudget (BinaryArithmetic.toNat q.ambient)
  (Finset.card (highSet q)) (Circuit.Model.val model 33) (Circuit.Model.val model 34) (Circuit.Model.val model 21) (Circuit.Model.val model 42) A (A+S+2) work
local notation "highSpace" => HighQueryCorrect.loopSpace (BinaryArithmetic.toNat q.ambient)
  (Finset.card (highSet q)) (Circuit.Model.val model 33) (Circuit.Model.val model 34) (Circuit.Model.val model 42) A (A+S+2)

include entry hindex hwidth hvalues hSA hfront hblank hhidden in
/-- The complete accepted query and same-step replay update precisely788
with the canonical whole count, preserving every other caller word. -/
theorem accepted_replay :
    ∃ steps output,
      Eval (HighQueryProgram.accepted k) steps input output ∧
      steps+1 ≤ HighQueryCorrect.acceptedBudget frontCost (S+frontBudget)
        (Cp*(S+frontBudget+1)^dp) highCost (QueryHeadBudgets.compact A) ∧
      output.stacks = Function.update input.stacks 788 (countWord (literalCount q source hsource)) ∧
      StageSpace (HighQueryProgram.accepted k) (steps+1) input
        (max (HighQueryCorrect.space q S frontCost (S+frontBudget) 0
          (Cp*(S+frontBudget+1)^dp) highSpace (QueryHeadBudgets.compact A)) frameBound) := by
  have hr := Query.accepted_ready q (project erased)
    (HighQueryEntryShadow.cleanWork input entry.clean)
    (HighQueryEntryShadow.sources q input entry.sources) entry.unmarked entry.index
  have hw : ∀ i, ((HighCountSeed.initialized (result run.front run.prepared.output)
      run.prepared.seedRegs).stacks i).length ≤ A := by
    simpa only [Nat.max_zero] using seeded_bound run
  have hqsize : 3^(Circuit.Model.val model 34) ≤ A+S+2 :=
    (field_card_bound q k S run.padding run.guard (fun j => (hvalues j).1)).trans (by omega)
  have hfrontendCost : run.frontendSteps ≤ frontCost := by
    change run.data.frontendSteps ≤ frontCost
    have htime : run.data.frontendSteps + 1 ≤ frontBudget := run.frontend_time
    omega
  obtain ⟨steps,output,he,ht,hcount,hs⟩ :=
    HighQueryCorrect.accepted run.prepared RB 1 1 RI 1 entry.valid _ run.words
      run.frontend_state hr hindex source hsource hwidth A (A+S+2) hw
      (fun j => (hvalues j).2.trans hSA) (by omega) hqsize erased
      run.frontendSteps frontCost S run.frontend hfrontendCost
      (shadow_input_bound run) run.kept (HighQueryEntryShadow.accepted_discarded input hblank)
      (HighQueryEntryShadow.scratch input entry.scratch)
  obtain ⟨her,hcr,hsr⟩ := HighQueryReturnReplay.accepted he hcount hs hhidden
  exact ⟨steps,_,her,ht,hcr,hsr⟩

end AcceptedReplay


open NativeQueryInputBounds Statement

attribute [local irreducible] Execute.guardedModel

/-- The fixed marked query executes on every actual attained trial and every
clause mark. Its ETH runtime is independent of all retained caller lengths;
its same-run prefix cap counts those retained words explicitly. -/
theorem marked (k C0 d0 : ℕ) (hk : 2 ≤ k) :
    ∃ C E : ℝ, ∃ degree Cs es cutoff : ℕ,
      1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (word : List Bool) (base d a : State 40 896) (e : Fin F.length)
        (tail : List Bool) (frameBound : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      NativeLeafRun.commonBound n F.length B R ≤ C0*(N+1)^d0 →
      (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
        base.stacks i = []) →
      word.length = HashCandidates.payloadWidth F.length (SparseCode.distanceDenom F.length B) →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = HashGreedyProgram.encodedHistory
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
      d.stacks 778 = Encoding.encodeList id [word] → d.stacks 779 = [] →
      HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
        (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
          (SparseCode.distanceDenom F.length B) word))) a →
      let input := recordState a tail (Encoding.encodeNat e.val)
      (∀ i, i ∈ HighQueryProgram.Carried.words → (input.stacks i).length ≤ frameBound) →
      ∃ steps output,
        Eval (HighQueryProgram.marked k) steps input output ∧
        steps+1 ≤ Nat.ceil (runtimeBound C E degree N n) ∧
        output.stacks 323 = countWord
          (markedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
            (HashCandidates.normalize F.length (SparseCode.distanceDenom F.length B) word.reverse ::
              HashGreedyCNF.history (NativeLeafSemantics.indexed F)
                (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds)
            (fun i x => !(NativeLeafSemantics.indexed F i).eval x) e) ∧
        HashMassAdapter.workspace output = HashMassAdapter.workspace input ∧
        HashMassAdapter.read output = HashMassAdapter.read input ∧
        RecordPrograms.state HashMassAdapter.recordPorts output false true false
          (input.stacks 320) [] = output ∧ output.stacks 324 = [] ∧
        (output.stacks 323).length ≤ n+1 ∧
        StageSpace (HighQueryProgram.marked k) (steps+1) input
          (max (Cs*(N+1)^es) frameBound) := by
  obtain ⟨Cp,dp,Cn,dn,Cl,dl,Cf,df,Nsetup,hsetup⟩ := NativeHashQuerySetup.marked_with_shadow k hk
  obtain ⟨Nrecord,hrecord⟩ := HashQueryParameterBounds.trial_envelope k 1 1 1 1 1 hk
  obtain ⟨C,E,degree,Ntime,hC,hE,hdegree,htime⟩ :=
    NativeQueryTimeBounds.runtime_bound k (2*(k-1)+1) (4*k+3) 17
      Cp dp Cn dn Cl dl Cf df C0 d0
  obtain ⟨Cs,es,hspace⟩ := NativeQuerySpaceBounds.shadow_polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  refine ⟨C,E,degree,Cs,es,max (max Nsetup Nrecord) Ntime,hC,hE,hdegree,?_⟩
  intro n N R hcut hN B F hv hm hmb shifts Q rounds hr word base d a e tail frameBound
    hbaseReady hbase hformula hamb hL hupper hword hframe hhistory hcounter hscratch hready input hhidden
  let q := trialQuery F hm shifts Q rounds word e d
  let L := NativeLeafRun.commonBound n F.length B R
  let S := sourceCap Cn dn Cl dl N L k
  let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
  let A := 12*P+4*N+6
  obtain ⟨entry,hqn,hindex,_hS,_hnS,_hiS,hvalues,hfront,_original,⟨run⟩⟩ :=
    hsetup n N R (by omega) hN F hv hm hmb shifts Q rounds hr word base d a e tail frameBound
      hbaseReady hbase hformula hamb hword hframe hhistory hcounter hscratch hready hhidden
  have hSA : S ≤ A := by
    dsimp only [A,P,preparedCap,HighQuerySetup.localBound]
    omega
  have h783 : d.stacks 783 = base.stacks 783 :=
    hframe 783 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h782 : d.stacks 782 = base.stacks 782 :=
    hframe 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h785 : d.stacks 785 = base.stacks 785 :=
    hframe 785 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_valid,_ambient,_scan,_small,henvelope⟩ :=
    hrecord n (by omega) F hv hm hmb shifts Q rounds hr word e d
      (by rw [h783,hbaseReady.width]; exact hbaseReady.modulus_length)
      (by rw [h782]; exact hbaseReady.clauses) (h785 ▸ hamb)
  let resource := ofPacking q k B 1 1 (2*(k-1)+1) 1 run.guard run.prepared.first run.prepared.rest
  have hresource : CostAssembly.Bounds (2*(k-1)+1) (4*k+3) 17 n resource :=
    (henvelope run.guard run.prepared.first run.prepared.rest run.prepared.nodup run.prepared.complete).1
  have hhigh : (highSet q).card ≤ n := by
    have h := Finset.card_le_univ (highSet q)
    simpa only [Fintype.card_fin,← hqn] using h
  have hhighEq : (highSet q).card = resource.branchVars := by
    simpa only [resource, ofPacking, make] using (high_mask_count q).symm
  have hhighQ : (highSet q).card ≤ BinaryArithmetic.toNat q.ambient := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (highSet q)
  have hb := htime (ambient q) (by rw [hqn]; omega) N L (hqn.trans_le hN) hL resource
    (by rw [hqn]; exact hresource)
    (HighMarkedFrontend.budget q k)
    ((Execute.guardedModel (q.input k) run.padding).val 33)
    ((Execute.guardedModel (q.input k) run.padding).val 34)
    ((Execute.guardedModel (q.input k) run.padding).val 21)
    ((Execute.guardedModel (q.input k) run.padding).val 42) (highSet q).card
    hfront (hvalues _ 33).2 (hvalues _ 34).2 (hvalues _ 21).2 (hvalues _ 42).2 hhighQ hhighEq
  have hs := hspace N L q (ambient q) (highSet q).card
    ((Execute.guardedModel (q.input k) run.padding).val 33)
    ((Execute.guardedModel (q.input k) run.padding).val 34)
    ((Execute.guardedModel (q.input k) run.padding).val 42) (HighMarkedFrontend.budget q k)
    hL rfl (hqn.trans_le hN) hhighQ (hvalues _ 33).2 (hvalues _ 34).2 (hvalues _ 42).2 hfront
  let source : RawCNF (BinaryArithmetic.toNat q.ambient) := Eq.mp (congrArg RawCNF hqn.symm) F
  have hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source :=
    HashQueryCount.rawQuery_source_bytes F hqn.symm _ _ _ _ _ _
  obtain ⟨hblank,_htmp⟩ := marked_entry_blank base d a word tail (Encoding.encodeNat e.val)
    hbaseReady hframe hupper hready
  obtain ⟨steps,output,he,ht,hcount,hws,hread,hreset,h324,htrace⟩ :=
    marked_replay run B (2*(k-1)+1) (frontendCap Cf df L k) frameBound _ entry hindex
      source hsource (source_width F hqn.symm hv) (hvalues run.padding) hSA hfront hblank hhidden
  have ht' : steps+1 ≤ Nat.ceil (runtimeBound C E degree N n) := by
    have hbound := hb.1
    have hreal : ((steps+1 : ℕ) : ℝ) ≤ runtimeBound C E degree N n := by
      have hh : ((steps+1 : ℕ) : ℝ) ≤ _ := Nat.cast_le.mpr ht
      exact (hh.trans hbound).trans_eq (congrArg (runtimeBound C E degree N) hqn)
    exact_mod_cast hreal.trans (Nat.le_ceil _)
  have hlen : (output.stacks 323).length ≤ n+1 := by
    rw [hcount]
    apply countWord_length_le
    exact (literalCount_le q source hsource).trans_eq (congrArg (fun x : ℕ => 2^x) hqn)
  have hc := literal_trial_count F hm shifts Q rounds word e d hqn.symm hsource
  rw [hc,HashGreedyCandidate.candidate_at_word word hword] at hcount
  refine ⟨steps,output,he,ht',hcount,hws,hread,hreset,h324,hlen,?_⟩
  constructor
  intro t z htz hz i
  exact (htrace.bound t z htz hz i).trans (max_le_max_right frameBound (by
    simpa only [NativeQuerySpaceBounds.querySpace] using hs))

/-- The fixed final query counts precisely the attained history at the
original ambient dimension. Every retained caller byte is restored, and the
canonical full count is the only changed word788. -/
theorem accepted (k C0 d0 : ℕ) (hk : 2 ≤ k) :
    ∃ C E : ℝ, ∃ degree Cs es cutoff : ℕ,
      1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (base d : State 40 896) (frameBound : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      NativeLeafRun.commonBound n F.length B R ≤ C0*(N+1)^d0 →
      (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
        base.stacks i = []) →
      HashGreedyRound.RowBoundary base
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d →
      let input := AcceptedQueryStage.staged d
      (∀ i, i ∈ HighQueryProgram.Carried.words → (input.stacks i).length ≤ frameBound) →
      ∃ steps output,
        Eval (HighQueryProgram.accepted k) steps input output ∧
        steps+1 ≤ Nat.ceil (runtimeBound C E degree N n) ∧
        output.stacks = Function.update input.stacks 788 (countWord
          (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
            (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
              (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))) ∧
        (output.stacks 788).length ≤ n+1 ∧
        StageSpace (HighQueryProgram.accepted k) (steps+1) input
          (max (Cs*(N+1)^es) frameBound) := by
  obtain ⟨Cp,dp,Cn,dn,Cl,dl,Cf,df,Nsetup,hsetup⟩ := NativeHashQuerySetup.accepted_with_shadow k hk
  obtain ⟨Nrecord,hrecord⟩ := HashQueryParameterBounds.accepted_envelope k 1 1 1 1 1 hk
  obtain ⟨C,E,degree,Ntime,hC,hE,hdegree,htime⟩ :=
    NativeQueryTimeBounds.runtime_bound k (2*(k-1)+1) (4*k+3) 17
      Cp dp Cn dn Cl dl Cf df C0 d0
  obtain ⟨Cs,es,hspace⟩ := NativeQuerySpaceBounds.shadow_polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  refine ⟨C,E,degree,Cs,es,max (max Nsetup Nrecord) Ntime,hC,hE,hdegree,?_⟩
  intro n N R hcut hN B F hv hm hmb shifts Q rounds hr base d frameBound
    hbaseReady hbase hformula hamb hL hupper hselected input hhidden
  let q := acceptedQuery F hm shifts Q rounds d
  let L := NativeLeafRun.commonBound n F.length B R
  let S := sourceCap Cn dn Cl dl N L k
  let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
  let A := 12*P+4*N+6
  obtain ⟨entry,hqn,hindex,_hS,_hnS,_hiS,hvalues,hfront,_original,⟨run⟩⟩ :=
    hsetup n N R (by omega) hN F hv hm hmb shifts Q rounds hr base d frameBound
      hbaseReady hbase hformula hamb hselected hhidden
  have hSA : S ≤ A := by
    dsimp only [A,P,preparedCap,HighQuerySetup.localBound]
    omega
  have h783 : d.stacks 783 = base.stacks 783 := hselected.frame 783 (by decide) (by decide)
  have h782 : d.stacks 782 = base.stacks 782 := hselected.frame 782 (by decide) (by decide)
  have h785 : d.stacks 785 = base.stacks 785 := hselected.frame 785 (by decide) (by decide)
  obtain ⟨_valid,_ambient,_scan,_small,henvelope⟩ :=
    hrecord n (by omega) F hv hm hmb shifts Q rounds hr d
      (by rw [h783,hbaseReady.width]; exact hbaseReady.modulus_length)
      (by rw [h782]; exact hbaseReady.clauses) (h785 ▸ hamb)
  let resource := ofPacking q k B 1 1 (2*(k-1)+1) 1 run.guard run.prepared.first run.prepared.rest
  have hresource : CostAssembly.Bounds (2*(k-1)+1) (4*k+3) 17 n resource :=
    (henvelope run.guard run.prepared.first run.prepared.rest run.prepared.nodup run.prepared.complete).1
  have hhigh : (highSet q).card ≤ n := by
    have h := Finset.card_le_univ (highSet q)
    simpa only [Fintype.card_fin,← hqn] using h
  have hhighEq : (highSet q).card = resource.branchVars := by
    simpa only [resource, ofPacking, make] using (high_mask_count q).symm
  have hhighQ : (highSet q).card ≤ BinaryArithmetic.toNat q.ambient := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (highSet q)
  have hb := htime (ambient q) (by rw [hqn]; omega) N L (hqn.trans_le hN) hL resource
    (by rw [hqn]; exact hresource)
    (HighMarkedFrontend.acceptedBudget q k)
    ((Execute.guardedModel (q.input k) run.padding).val 33)
    ((Execute.guardedModel (q.input k) run.padding).val 34)
    ((Execute.guardedModel (q.input k) run.padding).val 21)
    ((Execute.guardedModel (q.input k) run.padding).val 42) (highSet q).card
    hfront (hvalues _ 33).2 (hvalues _ 34).2 (hvalues _ 21).2 (hvalues _ 42).2 hhighQ hhighEq
  have hs := hspace N L q (ambient q) (highSet q).card
    ((Execute.guardedModel (q.input k) run.padding).val 33)
    ((Execute.guardedModel (q.input k) run.padding).val 34)
    ((Execute.guardedModel (q.input k) run.padding).val 42) (HighMarkedFrontend.acceptedBudget q k)
    hL rfl (hqn.trans_le hN) hhighQ (hvalues _ 33).2 (hvalues _ 34).2 (hvalues _ 42).2 hfront
  let source : RawCNF (BinaryArithmetic.toNat q.ambient) := Eq.mp (congrArg RawCNF hqn.symm) F
  have hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source :=
    HashQueryCount.rawQuery_source_bytes F hqn.symm _ _ _ _ _ _
  have hblank := NativeLeafRun.accepted_entry_discarded_blank base d hbaseReady hupper hselected
  obtain ⟨steps,output,he,ht,hcount,htrace⟩ :=
    accepted_replay run B (2*(k-1)+1) (frontendCap Cf df L k) frameBound entry hindex
      source hsource (source_width F hqn.symm hv) (hvalues run.padding) hSA hfront
      (fun i _ hi => hblank i hi) hhidden
  have ht' : steps+1 ≤ Nat.ceil (runtimeBound C E degree N n) := by
    have hbound := hb.2
    have hreal : ((steps+1 : ℕ) : ℝ) ≤ runtimeBound C E degree N n := by
      have hh : ((steps+1 : ℕ) : ℝ) ≤ _ := Nat.cast_le.mpr ht
      exact (hh.trans hbound).trans_eq (congrArg (runtimeBound C E degree N) hqn)
    exact_mod_cast hreal.trans (Nat.le_ceil _)
  have hlen : (output.stacks 788).length ≤ n+1 := by
    rw [hcount,Function.update_self]
    apply countWord_length_le
    exact (literalCount_le q source hsource).trans_eq (congrArg (fun x : ℕ => 2^x) hqn)
  have hc := literal_accepted_count F hm shifts Q rounds d hqn.symm hsource
  rw [hc] at hcount
  refine ⟨steps,output,he,ht',hcount,hlen,?_⟩
  constructor
  intro t z htz hz i
  exact (htrace.bound t z htz hz i).trans (max_le_max_right frameBound (by
    simpa only [NativeQuerySpaceBounds.querySpace] using hs))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries
