import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRunSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyBudgets

/-! Concrete leaf control: prepared code history, all physically staged greedy
rounds, and a separate history-only exact count. The query execution proofs
remain explicit development seams until the native query bodies instantiate them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

/-- The same fixed marked query runs for every visited greedy candidate. -/
def roundsCommand (markedQuery : Cmd 40 896) : Cmd 40 896 :=
  NativeRound.rounds (HashMassStaged.command markedQuery)

def afterPreparation (markedQuery acceptedQuery : Cmd 40 896) : Cmd 40 896 :=
  .seq (roundsCommand markedQuery) (AcceptedQueryStage.command acceptedQuery)

/-- No formula, successful code, or input-dependent table occurs in the code. -/
def command (markedQuery acceptedQuery : Cmd 40 896) : Cmd 40 896 :=
  .seq NativeLeafPreparation.command (afterPreparation markedQuery acceptedQuery)

def roundsTime (base : State 40 896) (n m depth : ℕ)
    (queryCost : List Bool → ℕ) (L : ℕ) : ℕ :=
  HashSelectProgram.roundsBudget
    (NativeRound.roundBudget
      (stagedAttemptBudget base n m depth queryCost L)
      (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth))
    (HashSelect.loopCap n m)

def roundsSpace (base : State 40 896) (n m depth L K : ℕ) : ℕ :=
  max (HashGreedyStagedSpace.attemptSpace base n m depth L K)
    (896 * L + 100 * (HashSelect.loopCap n m +
      HashCandidates.payloadWidth m depth + 1) +
      7 * (2 * HashCandidates.payloadWidth m depth + 3) + 20)

theorem ready_low {n m B : ℕ} {initial : List (List Bool)} {a : State 40 896}
    (hr : NativeLeafPreparation.Ready n m B initial a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] :=
  NativeCodeAssembly.worker_empty a hr.worker

theorem ready_core {n m B : ℕ} {initial : List (List Bool)} {a : State 40 896}
    (hr : NativeLeafPreparation.Ready n m B initial a) : CoreClean a := by
  constructor
  · exact hr.core 772 (by decide)
  · exact hr.core 773 (by decide)
  · exact hr.core 774 (by decide)
  · exact hr.core 775 (by decide)
  · exact hr.core 776 (by decide)

theorem ready_staging {n m B : ℕ} {initial : List (List Bool)} {a : State 40 896}
    (hr : NativeLeafPreparation.Ready n m B initial a) :
    ∀ i ∈ HashMassStaged.stagedPorts, a.stacks i = [] := by
  intro i hi
  apply ready_low hr i
  simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Physical readiness is supplied by the actual preparation theorem. The
execution and resource theorem use the identical staged attempt budget L. -/
theorem ready_rounds {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (initial : List (List Bool)) (depth : ℕ)
    (hd : depth = SparseCode.distanceDenom m B) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (base : State 40 896)
    (hr : NativeLeafPreparation.Ready n m B initial base)
    (L K : ℕ) (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : HashSelect.loopCap n m ≤ L)
    (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hgrowth : outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hbytesL : (encodedHistory initial).length +
      HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) ≤ L)
    (hq : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth word)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → (∀ i, (d.stacks i).length ≤ L) →
      ∀ (e : Fin m) tail a t middle,
      Ready (fun ws => ws = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      (read a).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      (Encoding.encodeNat e.val).length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse) K)
    : ∃ steps out, steps ≤ roundsTime base n m depth queryCost L ∧
      Eval (roundsCommand query) steps base out ∧
      RowBoundary base (HashGreedyCNF.history clauses depth
        initial (HashSelect.loopCap n m)) out ∧
      out.stacks 781 = [] ∧ out.regs 9 = false ∧
      (∀ i, (out.stacks i).length ≤ L) ∧
      StageSpace (roundsCommand query) (steps + 1) base (roundsSpace base n m depth L K) := by
  have hcounter : base.stacks 778 = Encoding.encodeList id
      [List.replicate (HashCandidates.payloadWidth m depth) false] := by
    rw [hd]
    exact hr.counter
  have hlo := ready_low hr
  have h0 := hr.core 768 (by decide)
  have h1 := hr.core 769 (by decide)
  have hbp := hr.core 770 (by decide)
  have hbs := hr.core 771 (by decide)
  have hcore := ready_core hr
  have hrounds : (base.stacks 781).length = HashSelect.loopCap n m := by
    simp only [hr.rounds, List.length_replicate]
  have hshape : (base.stacks 818).length = HashSelect.loopCap n m := by
    simp only [hr.shape, List.length_replicate]
  have hmw : CounterPrograms.value (base.stacks 782) = m := by
    rw [CounterPrograms.value_eq_toNat]
    exact hr.clauses
  have hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = [] := by
    intro i hi
    exact hlo i (by omega)
  have hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [] := by
    intro i _ hi
    exact hlo i (by omega)
  obtain ⟨steps,ht,out,he,hout,h781,h9⟩ := HashGreedyRun.staged_rounds_eval clauses hm
    initial query queryCost base hr.history hrounds h0 h1 hcore hbp hbs
    hcounter hr.scratch hlow (hlo 767 (by decide)) hr.modulus_length hr.modulus hmw hshape
    hcollector L (fun i _ => hbase i) hC hbytesL (ready_staging hr) hq
  have hs := HashGreedyRunSpace.rounds_halt_space clauses hm initial
    query queryCost base hr.history hrounds h0 h1 hcore hbp hbs hcounter hr.scratch hlow
    (hlo 767 (by decide)) hr.modulus_length hr.modulus hmw hshape hcollector L K hbase hB
    hcounterBound href hgrowth hC hbytesL (ready_staging hr) hq hspace he
  refine ⟨steps,out,ht,he,hout,h781,h9,?_,hs⟩
  intro i
  by_cases h777 : i = 777
  · subst i
    rw [hout.history]
    exact (HashQueryInputBounds.history_bytes clauses depth
      initial (HashSelect.loopCap n m)).trans hbytesL
  by_cases h781' : i = 781
  · subst i
    simp only [h781, List.length_nil, Nat.zero_le]
  rw [hout.frame i h777 h781']
  exact hbase i

/-- One retained cap supplies every numerical hypothesis of ready_rounds.
It depends on physical input words and ordinary scalar dimensions, not time. -/
def commonBound (n m B wordBound : ℕ) : ℕ :=
  16 * (HashQueryInputBounds.commonCap n m B wordBound) ^ 3

theorem common_bounds {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (wordBound : ℕ) :
    let L := commonBound n m B wordBound
    wordBound ≤ L ∧ HashSelect.loopCap n m ≤ L ∧
      HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ L ∧
      2 * HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) + 3 ≤ L ∧
      (encodedHistory (HashGreedyCode.initial shifts Q)).length + HashSelect.loopCap n m *
        (2 * HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) + 2) ≤ L ∧
      (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2 ∧
      outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2 ∧
      n + 1 ≤ L := by
  let S := HashQueryInputBounds.commonCap n m B wordBound
  obtain ⟨hS,hr,hg,hd,hw,hb,hW⟩ := HashQueryInputBounds.commonCap_bounds n m B wordBound
  have hn : n ≤ S := by dsimp [S,HashQueryInputBounds.commonCap]; omega
  have hm : m ≤ S := by dsimp [S,HashQueryInputBounds.commonCap]; omega
  obtain ⟨hround,hC,hcounter,hh,href,hgrowth,hnL⟩ :=
    HashQueryInputBounds.run_caps clauses shifts Q S hS hn hm hr hg hd hw hb
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  dsimp only [commonBound]
  change wordBound ≤ 16 * S ^ 3 ∧ _
  refine ⟨by omega,hround,hC,hcounter,hh,?_,?_,hnL⟩
  · change _ ≤ 3 * (16 * S ^ 3) + 2
    omega
  · change _ ≤ 3 * (16 * S ^ 3) + 2
    omega

/-- The final query is run on the saved history alone and its complete count
word is retained. The equality below never reads a single count bit as SAT. -/
theorem accepted_count {n B : ℕ} (F : DisjointReuse.RawCNF n)
    (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
    (query : Cmd 40 896) (base selected middle : State 40 896) (steps L K : ℕ)
    (hr : NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base)
    (hselected : RowBoundary base
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) selected)
    (ha : ∀ i, (selected.stacks i).length ≤ L) (hn : n + 1 ≤ L)
    (he : Eval query steps (AcceptedQueryStage.staged selected) middle)
    (hword : middle.stacks = Function.update (AcceptedQueryStage.staged selected).stacks 788
      (countWord (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
          (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)))))
    (hp : StageSpace query steps (AcceptedQueryStage.staged selected) K) :
    ∃ t out, t + 1 ≤ steps + 61 * L + 71 ∧
      Eval (AcceptedQueryStage.command query) t selected out ∧
      out.stacks = Function.update selected.stacks 788 (countWord (DisjointReuse.rawCount F)) ∧
      (∀ i, (out.stacks i).length ≤ L) ∧
      StageSpace (AcceptedQueryStage.command query) (t + 1) selected (max K (1000 * L + 100)) := by
  have hc := NativeLeafSemantics.history_count F hm hB shifts Q hs hQ
  rw [hc] at hword
  have hb : ∀ i, (middle.stacks i).length ≤ L := by
    intro i
    rw [hword]
    by_cases hi : i = 788
    · subst i
      rw [Function.update_self]
      exact (countWord_count_length (ExecCNF.formulaSet F)).trans hn
    rw [Function.update_of_ne hi]
    exact AcceptedQueryStage.staged_bound selected L ha i
  have ht : selected.stacks 767 = [] :=
    (hselected.frame 767 (by decide) (by decide)).trans (ready_low hr 767 (by decide))
  have hz : ∀ i ∈ HashMassStaged.stagedPorts, selected.stacks i = [] := by
    intro i hi
    have hne : i ≠ 777 ∧ i ≠ 781 := by
      simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hselected.frame i hne.1 hne.2).trans (ready_staging hr i hi)
  obtain ⟨heval,hcost,_htrace,_hcount,hbound,hprefix⟩ :=
    AcceptedQueryStage.run_of_eval query selected middle steps L K ha hb he hp.bound
  exact ⟨_,_,hcost,heval,AcceptedQueryStage.restored_stacks selected middle _ ht hz hword,
    hbound,⟨hprefix⟩⟩

/-- Compose the real rounds and real final query; each phase contributes its
independent storage cap rather than its duration. -/
theorem afterPreparation_eval (marked accepted : Cmd 40 896)
    (base selected out : State 40 896) (roundSteps querySteps roundCap queryCap : ℕ)
    (hr : Eval (roundsCommand marked) roundSteps base selected)
    (hq : Eval (AcceptedQueryStage.command accepted) querySteps selected out)
    (sr : StageSpace (roundsCommand marked) (roundSteps + 1) base roundCap)
    (sq : StageSpace (AcceptedQueryStage.command accepted) (querySteps + 1) selected queryCap) :
    Eval (afterPreparation marked accepted) (roundSteps + querySteps) base out ∧
      Trace (compiled (afterPreparation marked accepted) 784 788) (roundSteps + querySteps + 1)
        (base.withPC (some (compiled (afterPreparation marked accepted) 784 788).entry))
        (out.withPC none) ∧
      StageSpace (afterPreparation marked accepted) (roundSteps + querySteps + 1) base
        (max roundCap queryCap) := by
  have he := hr.seq hq
  refine ⟨he,compiled_halt_trace he 784 788,⟨?_⟩⟩
  apply StructuredSpace.compiled_halt_stack_bound he 778 777
  exact StructuredSpace.sequence_stack_bound hr hq 778 777
    (fun k c hk hc i => (sr.bound k c (by omega) hc i).trans (Nat.le_max_left _ _))
    (fun k c hk hc i => (sq.bound k c (by omega) hc i).trans (Nat.le_max_right _ _))
    _ _ _ (compiled_site _ 778 777)

/-- The actual preparation prefix and complete count suffix form one source
program. This theorem includes the final source halt before primitive lifting. -/
theorem command_of_evals (marked accepted : Cmd 40 896)
    (a prepared out : State 40 896) (prepareSteps runSteps prepareCap runCap : ℕ)
    (hp : Eval NativeLeafPreparation.command prepareSteps a prepared)
    (hr : Eval (afterPreparation marked accepted) runSteps prepared out)
    (sp : ∀ k c, k ≤ prepareSteps → Trace (compiled NativeLeafPreparation.command 784 788) k
      (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ prepareCap)
    (sr : StageSpace (afterPreparation marked accepted) (runSteps + 1) prepared runCap) :
    Eval (command marked accepted) (prepareSteps + runSteps) a out ∧
      Trace (compiled (command marked accepted) 784 788) (prepareSteps + runSteps + 1)
        (a.withPC (some (compiled (command marked accepted) 784 788).entry)) (out.withPC none) ∧
      ∀ k c, k ≤ prepareSteps + runSteps + 1 → Trace (compiled (command marked accepted) 784 788) k
        (a.withPC (some (compiled (command marked accepted) 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max prepareCap runCap := by
  have he := hp.seq hr
  refine ⟨he,compiled_halt_trace he 784 788,?_⟩
  apply StructuredSpace.compiled_halt_stack_bound he 784 788
  exact StructuredSpace.sequence_stack_bound hp hr 784 788
    (fun k c hk hc i => (sp k c hk hc i).trans (Nat.le_max_left _ _))
    (fun k c hk hc i => (sr.bound k c (by omega) hc i).trans (Nat.le_max_right _ _))
    _ _ _ (compiled_site _ 784 788)

/-- The first query really starts with the upper query work banks empty.
The premise is the literal frame returned by preparation and the actual
cleared input bank; readiness alone is deliberately not used for this fact. -/
theorem prepared_query_workspace (a prepared : State 40 896)
    (hframe : ∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) →
      prepared.stacks i = a.stacks i)
    (ha : ∀ i : Fin 896, 788 ≤ i.val → a.stacks i = []) :
    ∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
      prepared.stacks i = [] := by
  intro i hi
  rw [hframe i (by omega) (by omega)]
  exact ha i (by omega)

theorem rounds_query_workspace (base out : State 40 896) (rows : List (List Bool))
    (hr : RowBoundary base rows out)
    (hb : ∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
      base.stacks i = []) :
    ∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
      out.stacks i = [] := by
  intro i hi
  have hn (j : Fin 896) (hj : j.val < 788) : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  exact (hr.frame i (hn 777 (by decide)) (hn 781 (by decide))).trans (hb i hi)

/-- Exact raw count, literal tape word, measured source duration and uniform
source-prefix storage for the actual greedy-plus-accepted-query suffix. -/
theorem continuation_count {n B : ℕ} (F : DisjointReuse.RawCNF n)
    (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
    (marked accepted : Cmd 40 896) (base selected middle : State 40 896)
    (roundSteps querySteps L roundCap queryCap : ℕ)
    (hr : NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base)
    (hselected : RowBoundary base
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) selected)
    (ha : ∀ i, (selected.stacks i).length ≤ L) (hn : n + 1 ≤ L)
    (er : Eval (roundsCommand marked) roundSteps base selected)
    (sr : StageSpace (roundsCommand marked) (roundSteps + 1) base roundCap)
    (eq : Eval accepted querySteps (AcceptedQueryStage.staged selected) middle)
    (hword : middle.stacks = Function.update (AcceptedQueryStage.staged selected).stacks 788
      (countWord (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
          (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)))))
    (sq : StageSpace accepted querySteps (AcceptedQueryStage.staged selected) queryCap) :
    ∃ steps out, steps + 1 ≤ roundSteps + querySteps + 61 * L + 71 ∧
      Eval (afterPreparation marked accepted) steps base out ∧
      out.stacks = Function.update selected.stacks 788 (countWord (DisjointReuse.rawCount F)) ∧
      out.stacks 788 = countWord (DisjointReuse.rawCount F) ∧
      (∀ i, (out.stacks i).length ≤ L) ∧
      Trace (compiled (afterPreparation marked accepted) 784 788) (steps + 1)
        (base.withPC (some (compiled (afterPreparation marked accepted) 784 788).entry))
        (out.withPC none) ∧
      StageSpace (afterPreparation marked accepted) (steps + 1) base
        (max roundCap (max queryCap (1000 * L + 100))) := by
  obtain ⟨t,out,ht,he,hout,hbound,hprefix⟩ :=
    accepted_count F hm hB shifts Q hs hQ accepted base selected middle querySteps L queryCap
      hr hselected ha hn eq hword sq
  obtain ⟨whole,htrace,hspace⟩ := afterPreparation_eval marked accepted base selected out
    roundSteps t roundCap (max queryCap (1000 * L + 100)) er he sr hprefix
  exact ⟨_,out,by omega,whole,hout,by rw [hout,Function.update_self],hbound,htrace,hspace⟩

/-- The numerical comparison consumes the identical staged budget used by
ready_rounds. Its round word is a canonical mathematical representative of
the actual unary round count, not a second operational counter. -/
theorem roundsTime_le_fifth_power {n m B : ℕ} {initial : List (List Bool)}
    (base : State 40 896) (hr : NativeLeafPreparation.Ready n m B initial base)
    (hm : 0 < m) (queryCost : List Bool → ℕ) (L T : ℕ)
    (ha : ∀ i, (base.stacks i).length ≤ L)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    let depth := SparseCode.distanceDenom m B
    let S := m + depth + (n + 1) + L + HashSelect.loopCap n m + 1
    let E := Execution.Hash.polynomialBudget (base.stacks 780) (base.stacks 817)
      (countWord (HashSelect.loopCap n m)) (HashSelect.loopCap n m)
      (depth * (base.stacks 780).length) T
    roundsTime base n m depth queryCost L ≤ 1000000000 * (S + E + 1) ^ 5 := by
  have hc : CounterPrograms.value (base.stacks 780) = 3 * m := by
    rw [CounterPrograms.value_eq_toNat]
    exact hr.modulus
  have hmword : CounterPrograms.value (base.stacks 782) = m := by
    rw [CounterPrograms.value_eq_toNat]
    exact hr.clauses
  have h := HashGreedyBudgets.named_staged_rounds_le_fifth_power base
    (base.stacks 780) (base.stacks 817) (countWord (HashSelect.loopCap n m)) queryCost
    n m L T hm hc hmword (ha 0) (ha 782) (ha 769) ht
  simpa only [CounterPrograms.value_eq_toNat, hr.depth, countWord_toNat, roundsTime] using h

/-- Instantiate preparation on the exact raw DFS body. This exposes both
produced matrices and the actual blank first-query workspace from the loaded
three-word input, without a successful-code or layout premise. -/
theorem prepare_raw {n B W : ℕ} (F : DisjointReuse.RawCNF n) (a : State 40 896)
    (ha : ∀ i, (a.stacks i).length ≤ W)
    (hempty : ∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = [])
    (hformula : a.stacks 784 = DisjointReuse.SparseCountProgram.encodeBody F)
    (hm : F ≠ []) (hB : 0 < B)
    (hn : BinaryArithmetic.toNat (a.stacks 785) = n)
    (hBword : BinaryArithmetic.toNat (a.stacks 786) = B) :
    ∃ (steps : ℕ) (started prepared out : State 40 896)
      (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B),
      let L := W + NativeLeafSetup.canonicalStartTime n F.length W
      steps ≤ NativeLeafSetup.canonicalStartTime n F.length W +
        NativeLeafPreparation.continuationTime F.length B L started prepared ∧
      Eval NativeLeafPreparation.command steps a out ∧
      (∀ i, (started.stacks i).length ≤ L) ∧
      BinaryArithmetic.toNat (started.stacks 782) = F.length ∧
      BinaryArithmetic.toNat (started.stacks 768) = 3 * F.length ∧
      LeafOuterProgram.Metadata F.length B prepared ∧
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime F.length B L
        (started.stacks 782).length (started.stacks 786).length) ∧
      NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) out ∧
      WalshExistence.Good (SparseCode.gapDenom F.length B) shifts ∧
      SparseCode.HasDistance Q (SparseCode.degree F.length B /
        (100 * B * SparseCode.logSize F.length) + 1) ∧
      (∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ NativeLeafPreparation.retainedBound F.length B L started prepared) ∧
      (∀ k c, k ≤ steps → Trace (compiled NativeLeafPreparation.command 784 788) k
        (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (L + 1)
          (NativeLeafPreparation.continuationSpace F.length B L started prepared)) ∧
      ∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
        out.stacks i = [] := by
  generalize hlenF : F.length = m
  have hlenRecords : (NativeTerminal.clauseRecords F).length = m := by
    simpa only [NativeTerminal.clauseRecords, List.length_map] using hlenF
  rw [← hlenRecords]
  have hlo : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i = [] := by
    intro i hi
    have hne (j : Fin 896) (hj : 782 < j.val) : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      omega
    exact hempty i (hne 784 (by decide)) (hne 785 (by decide)) (hne 786 (by decide))
  have hencoded : a.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) :=
    hformula.trans (NativeTerminal.clauseRecords_body F).symm
  have hnonnil : NativeTerminal.clauseRecords F ≠ [] := by
    intro hz
    apply hm
    apply List.eq_nil_of_length_eq_zero
    have hlen := congrArg List.length hz
    simpa [NativeTerminal.clauseRecords] using hlen
  have h := NativeLeafPreparation.command_eval a (NativeTerminal.clauseRecords F)
    ha hlo hencoded hnonnil hB hn hBword
  obtain ⟨steps,started,prepared,out,shifts,Q,ht,he,hs,h782,h768,hmeta,hp,hr,hgood,hdist,
    hframe,hbound,hprefix⟩ := h
  refine ⟨steps,started,prepared,out,shifts,Q,ht,he,hs,h782,h768,hmeta,hp,hr,hgood,hdist,
    hframe,hbound,hprefix,prepared_query_workspace a out hframe ?_⟩
  intro i hi
  have hne (j : Fin 896) (hj : j.val < 788) : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  exact hempty i (hne 784 (by decide)) (hne 785 (by decide)) (hne 786 (by decide))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
