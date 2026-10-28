import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
import OAI.Algorithms.SubexponentialSAT.ProgramLogic

/-! Resource bounds for the actual outer DFS commands.

Cleanup is structurally nonallocating. The bounds below concern the concrete
finite tables and every source prefix, before applying the guarded primitive
compiler. The selector and leaf contracts still require their own executions.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource

open BitProgram StructuredCalls SparseDFSProgram

private theorem stackBits_single_le {S : ℕ} (words : Fin S → List Bool) (i : Fin S) :
    (words i).length ≤ stackBits words :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((words j).length)) (Finset.mem_univ i)

private theorem lifted_call_space {r s l steps localBound frameBound : ℕ}
    (routine : Program r s l) (register : Fin r ↪ Fin 80) (stack : Fin s ↪ Fin 1220)
    (frame : Data) {a b : State r s}
    (htrace : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hlocal : ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) c →
      ∀ i, (c.stacks i).length ≤ localBound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256)
        prefixSteps ((embedState register stack frame a).withPC
          (some (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ max localBound frameBound := by
  have hsource := StructuredSpace.liftProgram_stack_bound routine register stack
    (frame.withPC none) register.injective stack.injective htrace hlocal hframe
  have he := eval_call_lifted routine register stack frame register.injective stack.injective htrace
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (ProgramLinking.liftProgram routine register stack)
        (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256)
        (siteAddress (.call (ProgramLinking.liftProgram routine register stack)))
        (exitAddress (.call (ProgramLinking.liftProgram routine register stack)))
        (compiled_site (.call (ProgramLinking.liftProgram routine register stack)) 256 256) ht
      simpa only [ProgramLinking.embedCfg, ProgramLinking.relocatePc, embedState,
        StructuredProgram.State.withPC, id_eq] using hsource

theorem clearPort_space (port : Fin 1220) {steps bound : ℕ} {a b : Data}
    (he : Eval (clearPort port) steps a b)
    (hstart : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (clearPort port) 256 256) prefixSteps
        (a.withPC (some (compiled (clearPort port) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  cases he with
  | call p htrace =>
      apply StructuredSpace.call_stack_bound (StackRoutines.clearProgram port 0 1)
        (compiled (clearPort port) 256 256) (siteAddress (clearPort port))
        (exitAddress (clearPort port)) (compiled_site (clearPort port) 256 256) htrace
      intro prefixSteps c _ hc i
      exact (SparseDFSBoundarySpace.clearProgram_stack_length_le port 0 1 hc i).trans
        (hstart i)

/-- Sequential clearing keeps the same bound, including during every pop
and return jump. The finite list length never multiplies the space bound. -/
theorem clearPorts_space (ports : List (Fin 1220)) {steps bound : ℕ} {a b : Data}
    (he : Eval (clearPorts ports) steps a b)
    (hstart : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (clearPorts ports) 256 256) prefixSteps
        (a.withPC (some (compiled (clearPorts ports) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  induction ports generalizing steps a b with
  | nil =>
      cases he with
      | base h =>
          cases h with
          | skip =>
              intro prefixSteps c hp hc
              have hz : prefixSteps = 0 := by omega
              subst prefixSteps
              cases hc
              exact hstart
  | cons port rest ih =>
      cases he with
      | seq first second =>
          have hfirst := clearPort_space port first hstart
          have hmiddle := hfirst _ _ le_rfl (compiled_trace first 256 256)
          exact StructuredSpace.sequence_stack_bound first second 256 256 hfirst
            (ih second hmiddle) (compiled (clearPorts (port :: rest)) 256 256)
            (siteAddress (clearPorts (port :: rest)))
            (exitAddress (clearPorts (port :: rest))) (compiled_site (clearPorts (port :: rest)) 256 256)

theorem testPending_space (a : Data) (bound : ℕ)
    (hstart : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ 1 →
      Trace (compiled testPending 256 256) prefixSteps
        (a.withPC (some (compiled testPending 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  intro prefixSteps c hp hc
  have hcases : prefixSteps = 0 ∨ prefixSteps = 1 := by omega
  rcases hcases with rfl | rfl
  · cases hc
    exact hstart
  · rw [trace_same_length_unique hc (compiled_trace (testPending_eval a) 256 256)]
    exact hstart

/-- A complete visit cleanup clears the current formula and all 256 DFS
workspace stacks, preserves the other high words, and restores the loop flag
by reading the real frontier. Every intermediate stack remains bounded. -/
theorem finishVisit_execution_space (a : Data) (bound : ℕ)
    (hstart : ∀ i, (a.stacks i).length ≤ bound) :
    ∃ t ≤ (2 * bound + 3) * 257 + 1, ∃ e,
      Eval finishVisit t a e ∧
      (∀ i, i.val < 256 → e.stacks i = []) ∧ e.stacks 265 = [] ∧
      (∀ i, 256 ≤ i.val → i ≠ 265 → e.stacks i = a.stacks i) ∧
      e.regs 2 = (a.stacks 257).head?.getD false ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled finishVisit 256 256) prefixSteps
          (a.withPC (some (compiled finishVisit 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ bound := by
  let cleared : Data :=
    ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 265 a.stacks⟩
  have hclear : Eval (clearPort 265) (2 * (a.stacks 265).length + 3) a cleared :=
    clearPort_eval 265 a
  have hclear_space := clearPort_space 265 hclear hstart
  have hcleared : ∀ i, (cleared.stacks i).length ≤ bound :=
    hclear_space _ _ le_rfl (compiled_trace hclear 256 256)
  obtain ⟨lowTime, htime, afterLow, hlow, hempty, hframe, hlowBound⟩ :=
    clearLow_eval cleared bound hcleared
  let final : Data := ⟨readRegs afterLow.regs 2 1 (afterLow.stacks 257).head?, afterLow.stacks⟩
  have htest : Eval testPending 1 afterLow final := testPending_eval afterLow
  have hlow_space : ∀ prefixSteps c, prefixSteps ≤ lowTime →
      Trace (compiled clearLow 256 256) prefixSteps
        (cleared.withPC (some (compiled clearLow 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    simpa only [clearLow] using clearPorts_space lowPorts hlow hcleared
  have htest_space : ∀ prefixSteps c, prefixSteps ≤ 1 →
      Trace (compiled testPending 256 256) prefixSteps
        (afterLow.withPC (some (compiled testPending 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound :=
    testPending_space afterLow bound hlowBound
  have htail_space := StructuredSpace.sequence_stack_bound
    (first := clearLow) (second := testPending) (n := lowTime) (m := 1)
    (bound := bound) (a := cleared) (b := afterLow) (c := final)
    hlow htest 256 256
    hlow_space htest_space
    (compiled (.seq clearLow testPending) 256 256)
    (siteAddress (.seq clearLow testPending)) (exitAddress (.seq clearLow testPending))
    (compiled_site (.seq clearLow testPending) 256 256)
  have hfinish_space : ∀ prefixSteps c,
      prefixSteps ≤ 2 * (a.stacks 265).length + 3 + (lowTime + 1) →
      Trace (compiled finishVisit 256 256) prefixSteps
        (a.withPC (some (compiled finishVisit 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    exact StructuredSpace.sequence_stack_bound hclear (hlow.seq htest) 256 256
      hclear_space htail_space (compiled finishVisit 256 256)
      (siteAddress finishVisit) (exitAddress finishVisit)
      (compiled_site finishVisit 256 256)
  refine ⟨2 * (a.stacks 265).length + 3 + (lowTime + 1), ?_, final,
    hclear.seq (hlow.seq htest), hempty, ?_, ?_, ?_, ?_⟩
  · have h := hstart 265
    omega
  · change afterLow.stacks 265 = []
    rw [hframe 265 (by decide)]
    simp [cleared, StackRoutines.clearStacks]
  · intro i hi hne
    change afterLow.stacks i = a.stacks i
    rw [hframe i hi]
    simp [cleared, StackRoutines.clearStacks, hne]
  · have hpending : afterLow.stacks 257 = a.stacks 257 := by
      rw [hframe 257 (by decide)]
      simp [cleared, StackRoutines.clearStacks]
    simp [final, readRegs, hpending]
  · exact hfinish_space

/-- The concrete disjoint splitter and child insertion share one uniform
bound. Both child records, the pending list and every caller stack are counted;
no number of previously visited branches occurs in this bound. -/
theorem branch_execution_space (frame : Data) (regs : Fin 15 → Bool)
    (pending header : List Bool) (F S : List (List ℕ)) (H : List ℕ)
    (frameBound : ℕ) (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2, ∃ e,
      Eval branch t (embedState (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.inputState regs pending header F S H)) e ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled branch 256 256) prefixSteps
          ((embedState (registers 15 (by decide)) splitterStack frame
            (DisjointBranchProgram.inputState regs pending header F S H)).withPC
              (some (compiled branch 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max frameBound
          (pending.length + header.length + 620001 * (ExecCoreChildProgram.inputVolume F S H) ^ 2) := by
  let V := ExecCoreChildProgram.inputVolume F S H
  let bound := max frameBound (pending.length + header.length + 620001 * V ^ 2)
  let left := ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)
  let right := ExecCoreChildProgram.formulaCode
    (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H)
  let middle := embedState (registers 15 (by decide)) splitterStack frame
    (DisjointBranchProgram.outputState pending header F S H)
  have hv : 0 < V := by dsimp [V, ExecCoreChildProgram.inputVolume]; omega
  have hleft : left.length ≤ V := by
    have h := ExecCoreChildProgram.result_length_le F S H
    dsimp [left, V, ExecCoreChildProgram.inputVolume]
    omega
  have hright : right.length ≤ 5 * V := DisjointBranchProgram.resultB_length_le F S H
  obtain ⟨splitTime, htime, hsplitTrace⟩ := DisjointBranchProgram.program_runsIn regs pending header F S H
  have hsplit : Eval splitCurrent splitTime
      (embedState (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.inputState regs pending header F S H)) middle :=
    eval_call_lifted DisjointBranchProgram.program (registers 15 (by decide)) splitterStack
      frame (registers 15 (by decide)).injective splitterStack.injective hsplitTrace
  have hsplitLocal : ∀ t c, t ≤ splitTime →
      Trace DisjointBranchProgram.program t
        ((DisjointBranchProgram.inputState regs pending header F S H).withPC
          (some DisjointBranchProgram.program.entry)) c → ∀ i, (c.stacks i).length ≤ bound := by
    intro t c ht hc i
    have hb := DisjointBranchProgram.prefix_dataBits_le regs pending header F S H (ht.trans htime) hc
    have hi : (c.stacks i).length ≤ dataBits c :=
      stackBits_single_le c.stacks i
    exact (hi.trans hb).trans (Nat.le_max_right _ _)
  have hsplitSpace := lifted_call_space (frameBound := bound) DisjointBranchProgram.program (registers 15 (by decide))
    splitterStack frame hsplitTrace hsplitLocal
    (fun i => (hframe i).trans (Nat.le_max_left frameBound _))
  simp only [max_self] at hsplitSpace
  have hmiddle : ∀ i, (middle.stacks i).length ≤ bound :=
    hsplitSpace splitTime _ le_rfl (compiled_trace hsplit 256 256)
  have hpairTrace := SparseFrontierProgram.pushPair_trace left right header pending
    false false false false
  have hpairLocal : ∀ t c, t ≤ 13 * right.length + 13 * left.length + 37 →
      Trace SparseFrontierProgram.pushPairProgram t
        ((ExecWorklistProgram.data false false false false pending header
          (ExecWorklistProgram.record left) (ExecWorklistProgram.record right)).withPC
            (some SparseFrontierProgram.pushPairProgram.entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    intro t c ht hc i
    have hb := SparseFrontierProgram.pushPair_prefix_space left right header pending
      false false false false t c ht hc
    have hi : (c.stacks i).length ≤ dataBits c :=
      stackBits_single_le c.stacks i
    have hsmall : pending.length + header.length + 15 * (left.length + right.length) + 41 ≤
        pending.length + header.length + 620001 * V ^ 2 := by nlinarith
    exact ((hi.trans hb).trans hsmall).trans (Nat.le_max_right _ _)
  have hpairSpace := lifted_call_space SparseFrontierProgram.pushPairProgram
    (registers 4 (by decide)) pairStack middle hpairTrace hpairLocal hmiddle
  have hproject := splitter_pair_projection frame pending header F S H
  change projectState (registers 4 (by decide)) pairStack middle =
    ExecWorklistProgram.data false false false false pending header
      (ExecWorklistProgram.record left) (ExecWorklistProgram.record right) at hproject
  rw [← hproject] at hpairTrace hpairSpace
  simp only [embedState_project _ _ _ (registers 4 (by decide)).injective pairStack.injective,
    max_self] at hpairSpace
  have hpair := eval_call_from_state SparseFrontierProgram.pushPairProgram
    (registers 4 (by decide)) pairStack middle (registers 4 (by decide)).injective
    pairStack.injective hpairTrace
  refine ⟨splitTime + (13 * right.length + 13 * left.length + 37), ?_, _, hsplit.seq hpair, ?_⟩
  · change splitTime ≤ 620000 * V ^ 2 at htime
    change splitTime + (13 * right.length + 13 * left.length + 37) ≤ 621000 * V ^ 2
    nlinarith
  · exact StructuredSpace.sequence_stack_bound hsplit hpair 256 256 hsplitSpace hpairSpace
      (compiled branch 256 256) (siteAddress branch) (exitAddress branch) (compiled_site branch 256 256)


/-- Frontier initialization moves the actual current formula into its escaped
record and retains the saved declared-variable word and every caller stack. -/
theorem startFrontier_execution_space (frame : Data) (bodyWord saved : List Bool)
    (v p flag : Bool) (frameBound : ℕ)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    Eval startFrontier (8 * bodyWord.length + 13)
      (embedState (registers 3 (by decide)) frontierStack frame
        (SparseFrontierProgram.state v p flag bodyWord saved [] []))
      (embedState (registers 3 (by decide)) frontierStack frame
        (SparseFrontierProgram.state true false flag [] saved
          (Encoding.encodeList id [bodyWord]) [])) ∧
    ∀ prefixSteps c, prefixSteps ≤ 8 * bodyWord.length + 13 →
      Trace (compiled startFrontier 256 256) prefixSteps
        ((embedState (registers 3 (by decide)) frontierStack frame
          (SparseFrontierProgram.state v p flag bodyWord saved [] [])).withPC
            (some (compiled startFrontier 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ max (saved.length + 9 * bodyWord.length + 13) frameBound := by
  have htrace := SparseFrontierProgram.initFrontier_trace bodyWord saved v p flag
  refine ⟨eval_call_lifted SparseFrontierProgram.initFrontierProgram
    (registers 3 (by decide)) frontierStack frame (registers 3 (by decide)).injective
    frontierStack.injective htrace, ?_⟩
  apply lifted_call_space SparseFrontierProgram.initFrontierProgram
    (registers 3 (by decide)) frontierStack frame htrace _ hframe
  intro t c ht hc i
  exact (stackBits_single_le c.stacks i).trans
    (SparseFrontierProgram.initFrontier_prefix_space bodyWord saved v p flag t c ht hc)

/-- A real nonempty frontier pop decodes only its head record. All 1220 root
stacks are included, and no earlier traversal time appears in the bound. -/
theorem popCurrent_execution_space (frame : Data) (bodyWord saved pending : List Bool)
    (v p flag : Bool) (frameBound : ℕ)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    Eval popCurrent (9 * bodyWord.length + 11)
      (embedState (registers 3 (by decide)) frontierStack frame
        (SparseFrontierProgram.state v p flag [] saved
          (true :: (Encoding.frame bodyWord ++ pending)) []))
      (embedState (registers 3 (by decide)) frontierStack frame
        (SparseFrontierProgram.state false false true bodyWord saved pending [])) ∧
    ∀ prefixSteps c, prefixSteps ≤ 9 * bodyWord.length + 11 →
      Trace (compiled popCurrent 256 256) prefixSteps
        ((embedState (registers 3 (by decide)) frontierStack frame
          (SparseFrontierProgram.state v p flag [] saved
            (true :: (Encoding.frame bodyWord ++ pending)) [])).withPC
              (some (compiled popCurrent 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤
        max (saved.length + pending.length + 11 * bodyWord.length + 13) frameBound := by
  have htrace := SparseFrontierProgram.popIfPresent_cons_trace bodyWord saved pending v p flag
  refine ⟨eval_call_lifted SparseFrontierProgram.popIfPresentProgram
    (registers 3 (by decide)) frontierStack frame (registers 3 (by decide)).injective
    frontierStack.injective htrace, ?_⟩
  apply lifted_call_space SparseFrontierProgram.popIfPresentProgram
    (registers 3 (by decide)) frontierStack frame htrace _ hframe
  intro t c ht hc i
  exact (stackBits_single_le c.stacks i).trans
    (SparseFrontierProgram.popIfPresent_prefix_space bodyWord saved pending v p flag t c ht hc)

/-- The root accumulator uses the same concrete addition/normalization trace.
The disjoint-mass premise bounds both canonical input words; the final count
is on physical port260 and both count scratch ports are empty. -/
theorem accumulate_execution_space (frame : Data) (regs : Fin 8 → Bool)
    (a b n frameBound : ℕ) (hcount : a + b ≤ 2 ^ n)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∃ t ≤ 100 * (n + 1), ∃ e,
      Eval accumulate t
        (embedState (registers 8 (by decide)) countStack frame
          (SparseCountProgram.Accumulator.state regs (binaryNat a) (binaryNat b))) e ∧
      e.stacks 260 = binaryNat (a + b) ∧ e.stacks 263 = [] ∧ e.stacks 30 = [] ∧
      (∀ i, i ≠ 260 → i ≠ 263 → i ≠ 30 → e.stacks i = frame.stacks i) ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled accumulate 256 256) prefixSteps
          ((embedState (registers 8 (by decide)) countStack frame
            (SparseCountProgram.Accumulator.state regs (binaryNat a) (binaryNat b))).withPC
              (some (compiled accumulate 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (100 * (n + 1)) frameBound := by
  obtain ⟨t, final, ht, htrace, houtput, hclear1, hclear2, hprefix⟩ :=
    SparseCountProgram.Accumulator.canonical_execution regs a b n hcount
  refine ⟨t, ht, embedState (registers 8 (by decide)) countStack frame final,
    eval_call_lifted SparseCountProgram.Accumulator.program (registers 8 (by decide))
      countStack frame (registers 8 (by decide)).injective countStack.injective htrace,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (embedState_stack (registers 8 (by decide)) countStack frame final
      countStack.injective 0).trans houtput
  · exact (embedState_stack (registers 8 (by decide)) countStack frame final
      countStack.injective 1).trans hclear1
  · exact (embedState_stack (registers 8 (by decide)) countStack frame final
      countStack.injective 2).trans hclear2
  · intro i h0 h1 h2
    apply embedState_stack_frame
    rintro ⟨j, rfl⟩
    fin_cases j
    · exact h0 rfl
    · exact h1 rfl
    · exact h2 rfl
  · apply lifted_call_space SparseCountProgram.Accumulator.program
      (registers 8 (by decide)) countStack frame htrace _ hframe
    intro prefixSteps c hp hc i
    exact (stackBits_single_le c.stacks i).trans (hprefix prefixSteps c hp hc)


/-- Cleanup restores the smaller loop-boundary bound even when the completed
callback used a larger transient workspace. Consequently that workspace bound
is not accumulated from one DFS visit to the next. -/
theorem finishVisit_boundary_space (a : Data) (boundaryBound space : ℕ)
    (hstart : ∀ i, (a.stacks i).length ≤ space)
    (hhigh : ∀ i, 256 ≤ i.val → i ≠ 265 → (a.stacks i).length ≤ boundaryBound) :
    ∃ t ≤ (2 * space + 3) * 257 + 1, ∃ e,
      Eval finishVisit t a e ∧
      (∀ i, (e.stacks i).length ≤ boundaryBound) ∧
      (∀ i, 256 ≤ i.val → i ≠ 265 → e.stacks i = a.stacks i) ∧
      e.regs 2 = (a.stacks 257).head?.getD false ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled finishVisit 256 256) prefixSteps
          (a.withPC (some (compiled finishVisit 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ space := by
  obtain ⟨t, ht, e, he, hlow, hcurrent, hframe, hflag, hprefix⟩ :=
    finishVisit_execution_space a space hstart
  refine ⟨t, ht, e, he, ?_, hframe, hflag, hprefix⟩
  intro i
  by_cases hi : i.val < 256
  · rw [hlow i hi]
    exact Nat.zero_le _
  · by_cases hcurrentPort : i = 265
    · subst i
      rw [hcurrent]
      exact Nat.zero_le _
    · have hge : 256 ≤ i.val := by omega
      rw [hframe i hge hcurrentPort]
      exact hhigh i hge hcurrentPort


/-- The real selector runs in the frozen root bank. Its semantic hit/miss
results and all-prefix storage bound come from the same local execution;
the final return instruction is included before relocation into the root. -/
theorem selectCurrent_execution_space {α : Type*} [DecidableEq α]
    (encode : α → List Bool) (hinjective : Function.Injective encode)
    (k : ℕ) (F : List (List α)) (base : List Bool)
    (initialLocal : SparsePriorityProgram.Selector.Data) (frame : Data) (frameBound : ℕ)
    (hlocal : SparsePriorityProgram.Selector.Boundary (F.map (List.map encode)) base initialLocal)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∃ t ≤ SparsePriorityProgram.Selector.selectorCoefficient k *
        SparsePriorityProgram.Selector.inputVolume (F.map (List.map encode)) base ^ 4,
      ∃ e : SparsePriorityProgram.Selector.Data,
      Eval (selectCurrent k) (t + 1)
        (embedState (registers 24 (by decide)) selectorStack frame initialLocal)
        (embedState (registers 24 (by decide)) selectorStack frame e) ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = initialLocal.stacks i) ∧
      (e.regs 23 = false → e.stacks = initialLocal.stacks ∧
        ∀ c H, (c, H) ∈ SparsePriorityProgram.rawCandidates k F →
          0 < H.length → H.length < c →
          (SparsePriorityProgram.selectedRaw F c H).length <
            BinaryArithmetic.toNat base ^ (c - H.length)) ∧
      (e.regs 23 = true → ∃ c H,
        SparsePriorityProgram.RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        e.stacks 9 = SparsePriorityProgram.Filter.clauseCode (H.map encode) ∧
        e.stacks 12 = SparsePriorityProgram.Filter.formulaCode
          ((SparsePriorityProgram.selectedRaw F c H).map (List.map encode))) ∧
      ∀ prefixSteps c, prefixSteps ≤ t + 1 →
        Trace (compiled (selectCurrent k) 256 256) prefixSteps
          ((embedState (registers 24 (by decide)) selectorStack frame initialLocal).withPC
            (some (compiled (selectCurrent k) 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max
          ((SparsePriorityProgram.Selector.selectorCoefficient k + 24) *
            SparsePriorityProgram.Selector.inputVolume (F.map (List.map encode)) base ^ 4)
          frameBound := by
  obtain ⟨t, ht, e, he, hpreserve, hmiss, hhit, hspace⟩ :=
    SparsePriorityProgram.Selector.command_execution_map encode hinjective k F base initialLocal hlocal hwidth
  have htrace := compiled_halt_trace he 13 12
  have hhaltSpace := StructuredSpace.compiled_halt_stack_bound he 13 12 hspace
  refine ⟨t, ht, e, eval_call_lifted (SparsePriorityProgram.Selector.program k)
    (registers 24 (by decide)) selectorStack frame (registers 24 (by decide)).injective
    selectorStack.injective htrace, hpreserve, hmiss, hhit, ?_⟩
  exact lifted_call_space (SparsePriorityProgram.Selector.program k)
    (registers 24 (by decide)) selectorStack frame htrace hhaltSpace hframe


private theorem lifted_trace_stack_frame {r s l R S steps : ℕ}
    (routine : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    {a b : Cfg R S l} (htrace : Trace (ProgramLinking.liftProgram routine register stack) steps a b)
    (i : Fin S) (hoff : ¬ ∃ j, stack j = i) : b.stacks i = a.stacks i := by
  have hne : ∀ j, i ≠ stack j := fun j he => hoff ⟨j, he.symm⟩
  induction htrace with
  | refl => rfl
  | cons hstep _ ih =>
      apply ih.trans
      apply ProgramLogic.step_stack_frame (ProgramLinking.liftProgram routine register stack) i _ hstep
      intro label _
      change i ∉ ProgramLogic.stackWrites (ProgramLinking.relocateInstr register stack id none
        (routine.code label))
      cases routine.code label <;> simp [ProgramLinking.relocateInstr, ProgramLogic.stackWrites, hne]

/-- Every real branch execution preserves high words outside its fixed port
footprint. The header258 is handled separately by the splitter's exact header
readback; this structural rule covers raw input, leaf count, setup words and
all reserved high stacks for the very same branch witness. -/
theorem branch_preserves_other_high {steps : ℕ} {a b : Data}
    (he : Eval branch steps a b) (i : Fin 1220) (hi : 256 ≤ i.val)
    (hpending : i ≠ 257) (hheader : i ≠ 258) (hleft : i ≠ 261)
    (hright : i ≠ 262) (hcurrent : i ≠ 265) : b.stacks i = a.stacks i := by
  have hsplitOff : ¬ ∃ j, splitterStack j = i := by
    rintro ⟨j, rfl⟩
    have hrange := (by decide : ∀ q : Fin 23,
      (splitterStack q).val < 256 ∨ splitterStack q = 257 ∨ splitterStack q = 258 ∨
      splitterStack q = 261 ∨ splitterStack q = 262 ∨ splitterStack q = 265) j
    rcases hrange with h | h | h | h | h | h
    · omega
    · exact hpending h
    · exact hheader h
    · exact hleft h
    · exact hright h
    · exact hcurrent h
  have hpairOff : ¬ ∃ j, pairStack j = i := by
    rintro ⟨j, rfl⟩
    have hrange := (by decide : ∀ q : Fin 5,
      (pairStack q).val < 256 ∨ pairStack q = 257 ∨ pairStack q = 258 ∨
      pairStack q = 261 ∨ pairStack q = 262) j
    rcases hrange with h | h | h | h | h
    · omega
    · exact hpending h
    · exact hheader h
    · exact hleft h
    · exact hright h
  cases he with
  | seq hsplit hpair =>
      cases hsplit with
      | call _ hfirst =>
          cases hpair with
          | call _ hsecond =>
              exact (lifted_trace_stack_frame SparseFrontierProgram.pushPairProgram
                (registers 4 (by decide)) pairStack hsecond i hpairOff).trans
                (lifted_trace_stack_frame DisjointBranchProgram.program
                  (registers 15 (by decide)) splitterStack hfirst i hsplitOff)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource
