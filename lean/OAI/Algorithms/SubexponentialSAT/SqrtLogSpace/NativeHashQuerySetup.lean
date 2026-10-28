import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedSpec

/-! The actual prepared selector boundary supplies the literal marked and
history-only frontend, packing, arithmetic and high-counter initialization.
The common bound is unchanged. Suspended caller words have a separate bound
which never occurs in the measured setup time. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup

open BitProgram StructuredCalls SqrtLog DisjointReuse LeafParametersProgram
open HashGreedyCode HashQueryEntry HighFrontendSources NativeQueryInputBounds
open HighMarkedFrontend HighQuerySetup ProducedQueryResources
open HashGreedyProgram.NativeRound

abbrev Data := State 40 896

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

/-- Concrete frontend and preparation data for one setup run. A standard
dependent pair avoids generating a large custom recursor. -/
def SetupData (q : LeafQueryFrontend.Query) (k : ℕ) (frontBudget S B Cp dp : ℕ) : Type :=
  PSigma fun guard : Guard (q.input k) =>
    Σ _frontendSteps : ℕ, Σ front : Data, Σ padding : Fin 8 → ℕ, Σ _words : Bank.Words,
      PreparedRun q k guard front padding (S + frontBudget) B
        (Cp * (S + frontBudget + 1) ^ dp)

namespace SetupData

variable {q : LeafQueryFrontend.Query} {k frontBudget S B Cp dp : ℕ}

abbrev guard (data : SetupData q k frontBudget S B Cp dp) := data.fst
abbrev frontendSteps (data : SetupData q k frontBudget S B Cp dp) := data.snd.fst
abbrev front (data : SetupData q k frontBudget S B Cp dp) := data.snd.snd.fst
abbrev padding (data : SetupData q k frontBudget S B Cp dp) := data.snd.snd.snd.fst
abbrev words (data : SetupData q k frontBudget S B Cp dp) := data.snd.snd.snd.snd.fst
abbrev prepared (data : SetupData q k frontBudget S B Cp dp) :=
  data.snd.snd.snd.snd.snd

end SetupData

/-- Execution and resource facts referring to one concrete setup datum. -/
structure SetupFacts (q : LeafQueryFrontend.Query) (k : ℕ) (input : Data)
    (frontCommand : Cmd 40 896) (markerInput : State 40 768)
    (frontBudget S B Cp dp timeCap spaceCap : ℕ)
    (data : SetupData q k frontBudget S B Cp dp) : Prop where
  input_visible : ∀ i, ¬H i → (input.stacks i).length ≤ S
  frontend : Eval frontCommand data.frontendSteps input data.front
  frontend_time : data.frontendSteps + 1 ≤ frontBudget
  frontend_state : LeafProgram.Query.FrontState q k markerInput
    (project data.front) data.padding data.words
  eval : Eval (.seq frontCommand (.seq HighQueryProgram.prepare HighQueryProgram.seed))
    (data.frontendSteps + (data.prepared.packingSteps + data.prepared.arithmeticSteps + 1 +
      data.prepared.seedSteps)) input
    (HighCountSeed.initialized (result data.front data.prepared.output) data.prepared.seedRegs)
  time : data.frontendSteps +
    (data.prepared.packingSteps + data.prepared.arithmeticSteps + 1 +
      data.prepared.seedSteps) ≤ timeCap
  kept : ∀ i, HashMarkedReturn.kept i = true →
    (HighCountSeed.initialized (result data.front data.prepared.output)
      data.prepared.seedRegs).stacks i = input.stacks i
  space : StageSpace (.seq frontCommand (.seq HighQueryProgram.prepare HighQueryProgram.seed))
    (data.frontendSteps + (data.prepared.packingSteps + data.prepared.arithmeticSteps + 1 +
      data.prepared.seedSteps) + 1) input (max spaceCap B)

/-- A factual bundle of the same executed frontend and constructed setup.
The command and marker input are instantiated by the two concrete theorems. -/
def SetupRun (q : LeafQueryFrontend.Query) (k : ℕ) (input : Data)
    (frontCommand : Cmd 40 896) (markerInput : State 40 768)
    (frontBudget S B Cp dp timeCap spaceCap : ℕ) : Type :=
  { data : SetupData q k frontBudget S B Cp dp //
    SetupFacts q k input frontCommand markerInput frontBudget S B Cp dp timeCap spaceCap data }

namespace SetupRun

variable {q : LeafQueryFrontend.Query} {k : ℕ} {input : Data}
  {frontCommand : Cmd 40 896} {markerInput : State 40 768}
  {frontBudget S B Cp dp timeCap spaceCap : ℕ}

abbrev data (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.1
abbrev facts (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.2
abbrev guard (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.guard
abbrev frontendSteps (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.frontendSteps
abbrev front (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.front
abbrev padding (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.padding
abbrev words (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.words
abbrev prepared (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.prepared
abbrev input_visible (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.input_visible
abbrev frontend (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.frontend
abbrev frontend_time (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.frontend_time
abbrev frontend_state (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.frontend_state
abbrev eval (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.eval
abbrev time (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.time
abbrev kept (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.kept
abbrev space (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.space

end SetupRun

/-- The same actual frontend output has a visible cap independent of the
suspended caller words, suitable for the produced-source continuation. -/
theorem SetupRun.front_visible {q k input command marker budget S B Cp dp timeCap spaceCap}
    (run : SetupRun q k input command marker budget S B Cp dp timeCap spaceCap) :
    ∀ i, ¬ H i → (run.front.stacks i).length ≤ S + budget := by
  intro i hi
  have ht := trace_selectedStackBits (compiled command 778 777) {i}
    (compiled_trace run.frontend 778 777)
  have hlen : (run.front.stacks i).length ≤ (input.stacks i).length + run.frontendSteps := by
    simpa only [selectedStackBits, Finset.sum_singleton] using ht
  have hinput : (input.stacks i).length ≤ S := run.input_visible i hi
  have hsteps : run.frontendSteps ≤ budget :=
    (Nat.le_succ run.frontendSteps).trans run.frontend_time
  exact hlen.trans ((Nat.add_le_add_right hinput run.frontendSteps).trans
    (Nat.add_le_add_left hsteps S))

/-- Every actual callback has such a finite hidden cap. Choosing it imposes
no restriction on the collector tail, mass or remaining-round word. -/
def hiddenCap (a : Data) : ℕ :=
  HighQueryProgram.Carried.words.sup (fun i => (a.stacks i).length)

theorem hiddenCap_bound (a : Data) : ∀ i, H i → (a.stacks i).length ≤ hiddenCap a :=
  fun _ hi => Finset.le_sup (f := fun i => (a.stacks i).length) hi

private theorem shadow_visible (a : Data) (L : ℕ)
    (h : ∀ i, ((ProgramTapeReplay.rebaseState
      (fun i : Fin 896 => i.val = 320 ∨ i.val = 322 ∨ i.val = 770 ∨ i.val = 771 ∨ i.val = 781)
      (fun _ => []) a).stacks i).length ≤ L) :
    ∀ i, ¬ H i → (a.stacks i).length ≤ L := by
  intro i hi
  have hn : ¬(i.val = 320 ∨ i.val = 322 ∨ i.val = 770 ∨ i.val = 771 ∨ i.val = 781) := by
    simpa only [HighQueryProgram.Carried.words, Finset.mem_insert, Finset.mem_singleton,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod] using hi
  simpa only [ProgramTapeReplay.rebaseState,
    ProgramTapeReplay.rebaseStacks_of_not_mem
      (fun i : Fin 896 => i.val = 320 ∨ i.val = 322 ∨ i.val = 770 ∨ i.val = 771 ∨ i.val = 781)
      (fun _ => []) a.stacks i hn] using h i

/-- These are precisely the immutable physical facts needed by the numeric
input bounds, recovered from preparation and the actual six-port frame. -/
private theorem boundary_facts {n B R : ℕ} (F : RawCNF n)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (base d : Data)
    (hr : NativeLeafPreparation.Ready n F.length B (initial shifts Q) base)
    (hb : ∀ i, (base.stacks i).length ≤ R)
    (hformula : base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hamb : BinaryArithmetic.toNat (base.stacks 785) = n)
    (hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i) :
    (∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ R) ∧
    d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) ∧
    (d.stacks 783).length = HashCandidates.digitWidth F.length ∧
    BinaryArithmetic.toNat (d.stacks 782) = F.length ∧
    BinaryArithmetic.toNat (d.stacks 785) = n ∧
    LeafProgram.Query.CleanWork (project d) ∧ d.stacks 767 = [] := by
  have hm (i : Fin 896) (hi : 782 ≤ i.val) : d.stacks i = base.stacks i := by
    apply hf i <;> intro he <;> subst i <;> contradiction
  have hlo (i : Fin 896) (hi : i.val < 768) : d.stacks i = [] := by
    have hn (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
      intro he; subst j; omega
    rw [hf i (hn 770 (by decide)) (hn 771 (by decide)) (hn 777 (by decide))
      (hn 778 (by decide)) (hn 779 (by decide)) (hn 781 (by decide))]
    exact NativeLeafRun.ready_low hr i hi
  refine ⟨?_, (hm 784 (by decide)).trans hformula, ?_, ?_, ?_, ?_, hlo 767 (by decide)⟩
  · intro i hi
    rw [hm i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide)]
    exact hb i
  · rw [hm 783 (by decide), hr.width]; exact hr.modulus_length
  · rw [hm 782 (by decide)]; exact hr.clauses
  · rw [hm 785 (by decide)]; exact hamb
  · intro i _ _; exact hlo (stackMap i) i.isLt

/-- The real marked callback constructs its own frontend, packing and ring.
The arbitrary hidden bound is used only by the source-prefix conclusion. -/
theorem marked_with_shadow (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cp dp Cn dn Cl dl Cf df cutoff : ℕ,
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (word : List Bool) (base d a : Data) (e : Fin F.length) (tail : List Bool) (hidden : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
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
      (∀ i, H i → (input.stacks i).length ≤ hidden) →
      let q := trialQuery F hm shifts Q rounds word e d
      let L := NativeLeafRun.commonBound n F.length B R
      let S := sourceCap Cn dn Cl dl N L k
      let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
      MarkedEntry q (LeafOuterNative.trialStaged
        (HashGreedyExecution.trialState d F.length (SparseCode.distanceDenom F.length B) word)) input ∧
      ambient q = n ∧ q.index = Encoding.encodeNat (LeafProgram.PreparedSource.markIndex q) ∧
      1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
      (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
        (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
      HighMarkedFrontend.budget q k ≤ frontendCap Cf df L k ∧
      Nonempty (SetupRun q k input (HighMarkedFrontend.command k)
        (LeafProgram.Query.markedInput (project input)) (HighMarkedFrontend.budget q k)
        S hidden Cp dp (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) ∧
      Nonempty (SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.command k)
        (LeafProgram.Query.markedInput (project (HighQueryEntryShadow.erase input)))
        (HighMarkedFrontend.budget q k) S 0 Cp dp
        (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) := by
  obtain ⟨Cp,dp,hsetup⟩ := HighQuerySetup.marked
  obtain ⟨Cn,dn,Cl,dl,Cf,df,cutoff₁,hinputs⟩ := trial_inputs k hk
  obtain ⟨_Cg,_dg,cutoff₂,hguard⟩ := HashQueryParameterBounds.trial_numeric_caps k hk
  refine ⟨Cp,dp,Cn,dn,Cl,dl,Cf,df,max (max cutoff₁ cutoff₂) 1,?_⟩
  intro n N R hcut hN B F hv hm hmb shifts Q rounds hr word base d a e tail hidden
    hreadyBase hbase hformula hamb hword hframe hhistory hcounter hscratch hready input hhidden q L S P
  have hn : 0 < n := by omega
  obtain ⟨hmasters,hformula',hwidth,hmod,hamb',hclean,hscratch'⟩ :=
    boundary_facts F shifts Q base d hreadyBase hbase hformula hamb hframe
  have hentry := prepared_trial_entry F hn hm shifts Q rounds word base d a e tail
    hreadyBase hformula hamb hword hframe hhistory hready
  obtain ⟨_hvq,hqn,hS,hnS,hiS,hval,hlen,hfront,h3L⟩ := hinputs n N R (by omega) hN F hv hm hmb
    shifts Q rounds hr word d a e tail hword hmasters hformula' hhistory hwidth hmod hamb'
    hclean hscratch' hready
  obtain ⟨_,_,hscan,_⟩ := hguard n N (by omega) hN F hv hm hmb shifts Q rounds hr word e d hwidth hmod hamb'
  obtain ⟨hRL,_hround,_hC,hcounterBound,hbytes,href,_hgrowth,_hnL⟩ :=
    NativeLeafRun.common_bounds (NativeLeafSemantics.indexed F) shifts Q R
  have hhistoryBound : (d.stacks 777).length ≤ L := by
    rw [hhistory]
    exact (HashQueryInputBounds.history_bytes (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds).trans
      ((Nat.add_le_add_left (Nat.mul_le_mul_right _ hr) _).trans hbytes)
  have hshadow := HashQueryShadow.marked_shadow_bound_of_references base d a F.length
    (SparseCode.distanceDenom F.length B) L word tail e
    (fun i => (hbase i).trans hRL) hframe hhistoryBound hword hcounter hscratch hcounterBound href hready
  have hvisible : ∀ i, ¬ H i → (input.stacks i).length ≤ S :=
    fun i hi => (shadow_visible input (3*L+2) hshadow i hi).trans h3L
  obtain ⟨nf,front,padding,w,hfe,hft,hfs,run,he,ht,hkept,hspace⟩ :=
    hsetup q k hscan.guard input S hidden hentry.valid hentry.clean hentry.sources hentry.marked
      hentry.index hvisible hhidden (fun j => (hval _ j).1) hlen
  have hzvisible : ∀ i, ¬ H i → ((HighQueryEntryShadow.erase input).stacks i).length ≤ S := by
    intro i hi
    rw [HighQueryEntryShadow.visible input i hi]
    exact hvisible i hi
  have hzhidden : ∀ i, H i → ((HighQueryEntryShadow.erase input).stacks i).length ≤ 0 := by
    intro i hi
    simp [HighQueryEntryShadow.erase, ProgramTapeReplay.rebaseState,
      ProgramTapeReplay.rebaseStacks, hi]
  obtain ⟨nz,frontz,paddingz,wz,hfez,hftz,hfsz,runz,hez,htz,hkeptz,hspacez⟩ :=
    hsetup q k hscan.guard (HighQueryEntryShadow.erase input) S 0 hentry.valid
      (HighQueryEntryShadow.cleanWork input hentry.clean)
      (HighQueryEntryShadow.sources q input hentry.sources) hentry.marked
      (HighQueryEntryShadow.reference q input hentry.index) hzvisible hzhidden
      (fun j => (hval _ j).1) hlen
  refine ⟨hentry,hqn,?_,hS,hnS,hiS,hval,hfront,
    ⟨⟨⟨hscan.guard, nf, front, padding, w, run⟩, {
      input_visible := hvisible
      frontend := hfe
      frontend_time := hft
      frontend_state := hfs
      eval := he
      time := ?_
      kept := hkept
      space := ?_ }⟩⟩,
    ⟨⟨⟨hscan.guard, nz, frontz, paddingz, wz, runz⟩, {
      input_visible := hzvisible
      frontend := hfez
      frontend_time := hftz
      frontend_state := hfsz
      eval := hez
      time := ?_
      kept := hkeptz
      space := ?_ }⟩⟩⟩
  · simp [q, trialQuery, rawQueryFromRows, rawQuery, recordMark, LeafProgram.PreparedSource.markIndex]
  · exact ht.trans (setup_time_le Cp dp Cn dn Cl dl Cf df N L k _ hfront)
  · exact ⟨fun t z htz hz i => (hspace.bound t z htz hz i).trans
      (setup_prefix_bound_le q Cp dp Cn dn Cl dl Cf df N L k _ hidden hfront (hqn.trans_le hN))⟩
  · exact htz.trans (setup_time_le Cp dp Cn dn Cl dl Cf df N L k _ hfront)
  · exact ⟨fun t z htz' hz i => (hspacez.bound t z htz' hz i).trans
      (setup_prefix_bound_le q Cp dp Cn dn Cl dl Cf df N L k _ 0 hfront (hqn.trans_le hN))⟩

/-- The final history-only input constructs the same real setup without a
trial candidate or marked clause, at the unchanged prepared common bound. -/
theorem accepted_with_shadow (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cp dp Cn dn Cl dl Cf df cutoff : ℕ,
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (base d : Data) (hidden : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      HashGreedyRound.RowBoundary base
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d →
      let input := AcceptedQueryStage.staged d
      (∀ i, H i → (input.stacks i).length ≤ hidden) →
      let q := acceptedQuery F hm shifts Q rounds d
      let L := NativeLeafRun.commonBound n F.length B R
      let S := sourceCap Cn dn Cl dl N L k
      let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
      AcceptedEntry q input ∧ ambient q = n ∧
      q.index = Encoding.encodeNat (LeafProgram.PreparedSource.markIndex q) ∧
      1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
      (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
        (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
      HighMarkedFrontend.acceptedBudget q k ≤ frontendCap Cf df L k ∧
      Nonempty (SetupRun q k input (HighMarkedFrontend.acceptedCommand k)
        (LeafProgram.Query.unmarkedInput (project input)) (HighMarkedFrontend.acceptedBudget q k)
        S hidden Cp dp (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) ∧
      Nonempty (SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.acceptedCommand k)
        (LeafProgram.Query.unmarkedInput (project (HighQueryEntryShadow.erase input)))
        (HighMarkedFrontend.acceptedBudget q k) S 0 Cp dp
        (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) := by
  obtain ⟨Cp,dp,hsetup⟩ := HighQuerySetup.accepted
  obtain ⟨Cn,dn,Cl,dl,Cf,df,cutoff₁,hinputs⟩ := accepted_inputs k hk
  obtain ⟨_Cg,_dg,cutoff₂,hguard⟩ := HashQueryParameterBounds.accepted_numeric_caps k hk
  refine ⟨Cp,dp,Cn,dn,Cl,dl,Cf,df,max (max cutoff₁ cutoff₂) 1,?_⟩
  intro n N R hcut hN B F hv hm hmb shifts Q rounds hr base d hidden
    hreadyBase hbase hformula hamb hboundary input hhidden q L S P
  have hn : 0 < n := by omega
  have hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i :=
    fun i _ _ h777 _ _ h781 => hboundary.frame i h777 h781
  obtain ⟨hmasters,hformula',hwidth,hmod,hamb',hclean,_hscratch⟩ :=
    boundary_facts F shifts Q base d hreadyBase hbase hformula hamb hframe
  have hentry := prepared_accepted_entry F hn hm shifts Q rounds base d
    hreadyBase hformula hamb hboundary
  obtain ⟨_hvq,hqn,hS,hnS,hiS,hval,hlen,hfront,h3L⟩ := hinputs n N R (by omega) hN F hv hm hmb
    shifts Q rounds hr d hmasters hformula' hboundary.history hwidth hmod hamb' hclean
  obtain ⟨_,_,hscan,_⟩ := hguard n N (by omega) hN F hv hm hmb shifts Q rounds hr d hwidth hmod hamb'
  obtain ⟨hRL,_hround,_hC,_hcounterBound,hbytes,_href,_hgrowth,_hnL⟩ :=
    NativeLeafRun.common_bounds (NativeLeafSemantics.indexed F) shifts Q R
  have hhistoryBound : (HashGreedyProgram.encodedHistory
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds)).length ≤ L :=
    (HashQueryInputBounds.history_bytes (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds).trans
      ((Nat.add_le_add_left (Nat.mul_le_mul_right _ hr) _).trans hbytes)
  have hshadow := HashQueryShadow.accepted_shadow_bound base d _ L
    (fun i => (hbase i).trans hRL) hboundary hhistoryBound
  change 3*L+2 ≤ S at h3L
  have hvisible : ∀ i, ¬ H i → (input.stacks i).length ≤ S :=
    fun i hi => (shadow_visible input L hshadow i hi).trans (by omega)
  obtain ⟨nf,front,padding,w,hfe,hft,hfs,run,he,ht,hkept,hspace⟩ :=
    hsetup q k hscan.guard input S hidden hentry.valid hentry.clean hentry.sources hentry.unmarked
      hentry.index hvisible hhidden (fun j => (hval _ j).1) hlen
  have hzvisible : ∀ i, ¬ H i → ((HighQueryEntryShadow.erase input).stacks i).length ≤ S := by
    intro i hi
    rw [HighQueryEntryShadow.visible input i hi]
    exact hvisible i hi
  have hzhidden : ∀ i, H i → ((HighQueryEntryShadow.erase input).stacks i).length ≤ 0 := by
    intro i hi
    simp [HighQueryEntryShadow.erase, ProgramTapeReplay.rebaseState,
      ProgramTapeReplay.rebaseStacks, hi]
  obtain ⟨nz,frontz,paddingz,wz,hfez,hftz,hfsz,runz,hez,htz,hkeptz,hspacez⟩ :=
    hsetup q k hscan.guard (HighQueryEntryShadow.erase input) S 0 hentry.valid
      (HighQueryEntryShadow.cleanWork input hentry.clean)
      (HighQueryEntryShadow.sources q input hentry.sources) hentry.unmarked hentry.index
      hzvisible hzhidden (fun j => (hval _ j).1) hlen
  refine ⟨hentry,hqn,?_,hS,hnS,hiS,hval,hfront,
    ⟨⟨⟨hscan.guard, nf, front, padding, w, run⟩, {
      input_visible := hvisible
      frontend := hfe
      frontend_time := hft
      frontend_state := hfs
      eval := he
      time := ?_
      kept := hkept
      space := ?_ }⟩⟩,
    ⟨⟨⟨hscan.guard, nz, frontz, paddingz, wz, runz⟩, {
      input_visible := hzvisible
      frontend := hfez
      frontend_time := hftz
      frontend_state := hfsz
      eval := hez
      time := ?_
      kept := hkeptz
      space := ?_ }⟩⟩⟩
  · simp [q, acceptedQuery, rawQueryFromRows, rawQuery, recordMark,
      LeafProgram.PreparedSource.markIndex, Encoding.encodeNat]
  · exact ht.trans (setup_time_le Cp dp Cn dn Cl dl Cf df N L k _ hfront)
  · exact ⟨fun t z htz hz i => (hspace.bound t z htz hz i).trans
      (setup_prefix_bound_le q Cp dp Cn dn Cl dl Cf df N L k _ hidden hfront (hqn.trans_le hN))⟩
  · exact htz.trans (setup_time_le Cp dp Cn dn Cl dl Cf df N L k _ hfront)
  · exact ⟨fun t z htz' hz i => (hspacez.bound t z htz' hz i).trans
      (setup_prefix_bound_le q Cp dp Cn dn Cl dl Cf df N L k _ 0 hfront (hqn.trans_le hN))⟩

/-- Preserve the original concrete setup interface. The stronger theorem
also supplies the independently executed erased entry with the same constants. -/
theorem marked (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cp dp Cn dn Cl dl Cf df cutoff : ℕ,
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (word : List Bool) (base d a : Data) (e : Fin F.length) (tail : List Bool) (hidden : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
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
      (∀ i, H i → (input.stacks i).length ≤ hidden) →
      let q := trialQuery F hm shifts Q rounds word e d
      let L := NativeLeafRun.commonBound n F.length B R
      let S := sourceCap Cn dn Cl dl N L k
      let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
      MarkedEntry q (LeafOuterNative.trialStaged
        (HashGreedyExecution.trialState d F.length (SparseCode.distanceDenom F.length B) word)) input ∧
      ambient q = n ∧ q.index = Encoding.encodeNat (LeafProgram.PreparedSource.markIndex q) ∧
      1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
      (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
        (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
      HighMarkedFrontend.budget q k ≤ frontendCap Cf df L k ∧
      Nonempty (SetupRun q k input (HighMarkedFrontend.command k)
        (LeafProgram.Query.markedInput (project input)) (HighMarkedFrontend.budget q k)
        S hidden Cp dp (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) := by
  obtain ⟨Cp,dp,Cn,dn,Cl,dl,Cf,df,cutoff,h⟩ := marked_with_shadow k hk
  refine ⟨Cp,dp,Cn,dn,Cl,dl,Cf,df,cutoff,?_⟩
  intro n N R hcut hN B F hv hm hmb shifts Q rounds hr word base d a e tail hidden
    hreadyBase hbase hformula hamb hword hframe hhistory hcounter hscratch hready input hhidden q L S P
  obtain ⟨hentry,hqn,hindex,hS,hnS,hiS,hval,hfront,run,_shadow⟩ :=
    h n N R hcut hN F hv hm hmb shifts Q rounds hr word base d a e tail hidden
      hreadyBase hbase hformula hamb hword hframe hhistory hcounter hscratch hready hhidden
  exact ⟨hentry,hqn,hindex,hS,hnS,hiS,hval,hfront,run⟩

/-- Preserve the original concrete setup interface. The stronger theorem
also supplies the independently executed erased entry with the same constants. -/
theorem accepted (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cp dp Cn dn Cl dl Cf df cutoff : ℕ,
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (base d : Data) (hidden : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      HashGreedyRound.RowBoundary base
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d →
      let input := AcceptedQueryStage.staged d
      (∀ i, H i → (input.stacks i).length ≤ hidden) →
      let q := acceptedQuery F hm shifts Q rounds d
      let L := NativeLeafRun.commonBound n F.length B R
      let S := sourceCap Cn dn Cl dl N L k
      let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
      AcceptedEntry q input ∧ ambient q = n ∧
      q.index = Encoding.encodeNat (LeafProgram.PreparedSource.markIndex q) ∧
      1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
      (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
        (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
      HighMarkedFrontend.acceptedBudget q k ≤ frontendCap Cf df L k ∧
      Nonempty (SetupRun q k input (HighMarkedFrontend.acceptedCommand k)
        (LeafProgram.Query.unmarkedInput (project input)) (HighMarkedFrontend.acceptedBudget q k)
        S hidden Cp dp (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) := by
  obtain ⟨Cp,dp,Cn,dn,Cl,dl,Cf,df,cutoff,h⟩ := accepted_with_shadow k hk
  refine ⟨Cp,dp,Cn,dn,Cl,dl,Cf,df,cutoff,?_⟩
  intro n N R hcut hN B F hv hm hmb shifts Q rounds hr base d hidden
    hreadyBase hbase hformula hamb hboundary input hhidden q L S P
  obtain ⟨hentry,hqn,hindex,hS,hnS,hiS,hval,hfront,run,_shadow⟩ :=
    h n N R hcut hN F hv hm hmb shifts Q rounds hr base d hidden
      hreadyBase hbase hformula hamb hboundary hhidden
  exact ⟨hentry,hqn,hindex,hS,hnS,hiS,hval,hfront,run⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup
