import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge

/-! Actual state refinements for the fixed attained-signature controller.
Each lemma follows concrete commands already installed in the native ABI. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open SignatureTupleDFS SignatureTupleTraversal

noncomputable def retainedState (a : State 40 896) : State 40 896 :=
  saveCursorState (recordRepresentativeState a)

noncomputable def descendClearState (a : State 40 896) : State 40 896 :=
  clearWordsState currentHeadPorts (descendLevelState (retainedState a))

theorem recordRepresentative_outside (a : State 40 896) (i : Fin 896)
    (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (recordRepresentativeState a).stacks i = a.stacks i := by
  unfold recordRepresentativeState
  rw [pushWordState_outside _ _ _ _ _ hp hr]
  simp [copyState, StackRoutines.copyStacks, hp]

theorem retainedState_outside (a : State 40 896) (i : Fin 896)
    (h0 : i ≠ tupleStacks 0) (h1 : i ≠ tupleStacks 1)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (retainedState a).stacks i = a.stacks i := by
  unfold retainedState saveCursorState
  rw [pushWordState_outside _ _ _ _ _ h7 h0,
    pushWordState_outside _ _ _ _ _ h2 h0, recordRepresentative_outside a i h1 h4]

theorem retainedState_register (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) : (retainedState a).regs j = a.regs j := by
  unfold retainedState saveCursorState recordRepresentativeState
  rw [pushWordState_register_frame _ _ _ _ j h0 h1,
    pushWordState_register_frame _ _ _ _ j h0 h1,
    pushWordState_register_frame _ _ _ _ j h0 h1]
  exact StackRoutines.readRegs_frame a.regs 0 1 j none h0 h1

theorem descendLevelState_outside (a : State 40 896) (i : Fin 896)
    (h6 : i ≠ tupleStacks 6) (h9 : i ≠ tupleStacks 9) :
    (descendLevelState a).stacks i = a.stacks i := by
  simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, h6, h9]

theorem descendLevelState_active (a : State 40 896) :
    (descendLevelState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, readRegs,
    controllerPorts]

theorem descendClearState_cleared (a : State 40 896) :
    ∀ i ∈ currentHeadPorts, (descendClearState a).stacks i = [] := by
  intro i hi
  rw [descendClearState, clearWordsState_stacks, ite_eq_left hi]

theorem descendClearState_stack (a : State 40 896) (i : Fin 896)
    (hi : i ∉ currentHeadPorts) :
    (descendClearState a).stacks i = (descendLevelState (retainedState a)).stacks i := by
  rw [descendClearState, clearWordsState_stacks, ite_eq_right hi]

theorem descendClearState_active (a : State 40 896) :
    (descendClearState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  rw [descendClearState, clearWordsState_register_frame _ _ _ (by decide) (by decide),
    descendLevelState_active, retainedState_register _ _ (by decide) (by decide)]

theorem descendClearState_leaf (a : State 40 896) (address : ℕ)
    (hr : a.stacks (tupleStacks 6) = [true])
    (hz : a.stacks (tupleStacks 9) = List.replicate address true) :
    (descendClearState a).regs controllerPorts.leaf = true := by
  have hw := descendLevelState_words (retainedState a) 0 address
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr)
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz)
  rw [descendClearState, clearWordsState_register_frame _ _ _ (by decide) (by decide)]
  exact hw.2.2

theorem seq_reassociate {first second third : Cmd 40 896} {n : ℕ} {a b : State 40 896}
    (he : Eval (.seq (.seq first second) third) n a b) :
    Eval (.seq first (.seq second third)) n a b := by
  cases he with
  | seq hab hc =>
    cases hab with
    | seq ha hb => simpa only [Nat.add_assoc] using ha.seq (hb.seq hc)

/-- The last fresh representative reaches an actual leaf only after its
cursor is saved and all eight current-head tapes have been cleared. -/
theorem descend_leaf_eval (loadHead : Cmd 40 896) (a : State 40 896)
    (width candidate address : ℕ)
    (hc : a.stacks (tupleStacks 2) = ExecCNFTupleEnumeration.fixedBits width candidate)
    (hn : a.stacks (tupleStacks 7) =
      ExecCNFTupleEnumeration.fixedBits (width + 1) (2 ^ width - candidate))
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hr : a.stacks (tupleStacks 6) = [true])
    (hz : a.stacks (tupleStacks 9) = List.replicate address true) :
    Eval (descendWith loadHead)
      (22 * width + 31 + clearWordsTime currentHeadPorts (descendLevelState (retainedState a)))
      a (descendClearState a) := by
  have hf := retainFrames_eval width candidate a hc hn hp ht
  have hl := descendLevel_eval (retainedState a)
  have hclear := clearWords_eval currentHeadPorts (descendLevelState (retainedState a))
  have hbranch : Eval (.ite controllerPorts.leaf (.base .skip)
      (.seq loadHead resetGeneratorCommand)) 1 (descendClearState a) (descendClearState a) :=
    .ite_true (descendClearState_leaf a address hr hz) (.base (.skip _))
  have he := seq_reassociate (hf.seq (hl.seq (hclear.seq hbranch)))
  change Eval (descendWith loadHead) _ a (descendClearState a) at he
  convert he using 1
  omega


theorem counter_install_register_frame (p : CounterForPrograms.Ports 40 896)
    (a : State 40 896) (b present flag : Bool) (xs ys : List Bool) (j : Fin 40)
    (hj : ¬ ∃ i, p.register i = j) :
    (CounterForPrograms.install p a b present flag xs ys).regs j = a.regs j :=
  embedState_register_frame _ _ _ _ _ hj

theorem lowCounter_register_avoids (j : Fin 40) (hj : 3 ≤ j.val) :
    (¬ ∃ i, candidatePorts.register i = j) ∧
      (¬ ∃ i, remainingPorts.register i = j) := by
  constructor <;> rintro ⟨i, hi⟩
  all_goals
    have hv := congrArg Fin.val hi
    have hil := i.isLt
    dsimp [candidatePorts, remainingPorts] at hv
    omega

theorem advanceState_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (hav : j ≠ controllerPorts.available) :
    (advanceState a).regs j = a.regs j := by
  have h2 : j ≠ remainingPorts.register 2 := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [remainingPorts] at hv
    omega
  have hreg := lowCounter_register_avoids j hj
  unfold advanceState CounterForPrograms.nextState CounterForPrograms.testResult
  simp only [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    Function.update_of_ne hav, Function.update_of_ne h2]
  unfold CounterForPrograms.zeroResult
  rw [counter_install_register_frame _ _ _ _ _ _ _ j hreg.2]
  unfold CounterForPrograms.decrementResult
  rw [counter_install_register_frame _ _ _ _ _ _ _ j hreg.2]
  unfold Counters.incrementResult
  exact counter_install_register_frame _ _ _ _ _ _ _ j hreg.1

theorem advanceCandidateState_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (hav : j ≠ controllerPorts.available) :
    (advanceCandidateState a).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro he; have := congrArg Fin.val he; simp at this; omega
  have h1 : j ≠ 1 := by intro he; have := congrArg Fin.val he; simp at this; omega
  change readRegs (advanceState a).regs 0 1 none j = a.regs j
  rw [StackRoutines.readRegs_frame _ _ _ _ _ h0 h1]
  exact advanceState_register_frame a j hj hav

theorem advanceCandidateState_outside (a : State 40 896)
    (hs : a.stacks candidatePorts.scratch = []) (i : Fin 896)
    (hk : i ≠ tupleStacks 3) (hc : i ≠ candidatePorts.counter)
    (hr : i ≠ remainingPorts.counter) (ht : i ≠ remainingPorts.scratch) :
    (advanceCandidateState a).stacks i = a.stacks i := by
  change Function.update (advanceState a).stacks (tupleStacks 3) [] i = a.stacks i
  rw [Function.update_of_ne hk, advanceState_outside a hs i hc hr ht]

/-- The complete probe restores the same fixed boundary cap. Its larger
transient prefix bound is not fed back into the next iteration. -/
theorem probe_endpoint_bound (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h B F : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = [])
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hpositive : 1 ≤ F)
    (hkey : AttainedSignatureProgram.Rescan.keyBound W h rows.length B ≤ F) :
    ∀ i, ((probePostState a out W rows h candidate).stacks i).length ≤ F := by
  intro i
  rw [SignatureRescanBridge.probe_stacks a out W rows h candidate ready hs]
  by_cases hf : i = rescanStacks 22
  · subst i
    simpa only [Function.update_self, List.length_singleton] using hpositive
  · rw [Function.update_of_ne hf]
    by_cases hk : i = rescanStacks 17
    · subst i
      rw [Function.update_self]
      exact (AttainedSignatureProgram.Rescan.naturalKey_length_le W rows h B
        hlen hwidth candidate).trans hkey
    · rw [Function.update_of_ne hk]
      exact hframe i

/-- Counter advancement and key disposal also restore the original boundary
cap, including the terminal candidate whose word has one extra bit. -/
theorem advance_endpoint_bound (a : State 40 896) (h candidate F : ℕ)
    (hw : CursorWords a h candidate) (hc : candidate < 2 ^ h)
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hwidth : h + 1 ≤ F) :
    ∀ i, ((advanceCandidateState a).stacks i).length ≤ F := by
  have hn := hw.advance hc
  intro i
  by_cases hk : i = tupleStacks 3
  · subst i
    change (Function.update (advanceState a).stacks (tupleStacks 3) []
      (tupleStacks 3)).length ≤ F
    simp
  · by_cases hcan : i = candidatePorts.counter
    · subst i
      exact hn.width.trans hwidth
    · by_cases hrem : i = remainingPorts.counter
      · subst i
        rw [hn.remaining, ExecCNFTupleEnumeration.fixedBits_length]
        exact hwidth
      · by_cases hs : i = remainingPorts.scratch
        · subst i
          rw [hn.decrementScratch]
          simp
        · rw [advanceCandidateState_outside a hw.incrementScratch i hk hcan hrem hs]
          exact hframe i

/-- Scanner scratch is restored by each probe and is disjoint from both
binary counters. Thus advancing never requires a new allocation or scan. -/
theorem probe_advance_ready (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate next : Fin (2 ^ h)) (hnext : next.val = candidate.val + 1)
    (ready : CandidateReady a W rows h candidate) (hw : CursorWords a h candidate) :
    CandidateReady (advanceCandidateState (probePostState a out W rows h candidate))
      W rows h next := by
  let b := probePostState a out W rows h candidate
  have hb : CursorWords b h candidate :=
    SignatureRescanBridge.probe_preserves_cursor a out W rows h candidate ready hw
  have hn := hb.advance candidate.isLt
  have hf (i : Fin 896) (hk : i ≠ tupleStacks 3) (hc : i ≠ candidatePorts.counter)
      (hr : i ≠ remainingPorts.counter) (hs : i ≠ remainingPorts.scratch)
      (h17 : i ≠ rescanStacks 17) (h22 : i ≠ rescanStacks 22) :
      (advanceCandidateState b).stacks i = a.stacks i := by
    rw [advanceCandidateState_outside b hb.incrementScratch i hk hc hr hs]
    exact SignatureRescanBridge.probe_stack_frame a out W rows h candidate ready
      hw.decrementScratch i h17 h22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.offset
  · rw [hf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.matrix
  · change (advanceCandidateState b).stacks candidatePorts.counter = _
    rw [hnext]
    exact hn.exact (by rw [← hnext]; exact next.isLt)
  · change Function.update (advanceState b).stacks (tupleStacks 3) [] (tupleStacks 3) = []
    exact Function.update_self _ _ _
  · rw [hf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.predecessor
  · intro i h0 h15 h16 h17 h18 h22
    have hsmall : ∀ j : Fin 24, j ≠ 0 → j ≠ 15 → j ≠ 16 → j ≠ 17 → j ≠ 18 →
        (rescanStacks j).val < 768 := by decide
    have hv := hsmall i h0 h15 h16 h17 h18
    have hports : rescanStacks i ≠ tupleStacks 3 ∧
        rescanStacks i ≠ candidatePorts.counter ∧ rescanStacks i ≠ remainingPorts.counter ∧
        rescanStacks i ≠ remainingPorts.scratch ∧ rescanStacks i ≠ rescanStacks 17 ∧
        rescanStacks i ≠ rescanStacks 22 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro he; have he' := congrArg Fin.val he; change (rescanStacks i).val = 839 at he'; omega
      · intro he; have he' := congrArg Fin.val he; change (rescanStacks i).val = 838 at he'; omega
      · intro he; have he' := congrArg Fin.val he; change (rescanStacks i).val = 843 at he'; omega
      · intro he; have he' := congrArg Fin.val he; change (rescanStacks i).val = 841 at he'; omega
      · exact fun he => h17 (rescanStacks.injective he)
      · exact fun he => h22 (rescanStacks.injective he)
    rw [hf _ hports.1 hports.2.1 hports.2.2.1 hports.2.2.2.1
      hports.2.2.2.2.1 hports.2.2.2.2.2]
    exact ready.scratch i h0 h15 h16 h17 h18 h22

section AdvanceStorage

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- A completed candidate is advanced once. Its full key is discarded, while
both attained-prefix frame banks and the physical head address survive. -/
theorem advance_scan_storage (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (candidate : ℕ)
    (a : State 40 896)
    (ha : AncestorStorage h key levels base depth.val ancestors a)
    (hw : CursorWords a (h depth.val) candidate) (hc : candidate < 2 ^ h depth.val)
    (hl : a.regs controllerPorts.leaf = false)
    (hp : a.stacks (tupleStacks 4) = [])
    (hz : a.stacks (tupleStacks 8) = List.replicate (h depth.val) false) :
    ScanStorage h key levels base depth ancestors (candidate + 1) (advanceCandidateState a) := by
  have hwords := hw.advance hc
  have hframe (i : Fin 896) (hk : i ≠ tupleStacks 3) (hcan : i ≠ candidatePorts.counter)
      (hrem : i ≠ remainingPorts.counter) (hs : i ≠ remainingPorts.scratch) :
      (advanceCandidateState a).stacks i = a.stacks i :=
    advanceCandidateState_outside a hw.incrementScratch i hk hcan hrem hs
  refine ⟨⟨ha.depth_le, ?_, ?_, ?_, ?_, ?_⟩, hwords, ?_, ?_, ?_, ?_⟩
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact ha.cursors
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact ha.representatives
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact ha.heads
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact ha.address
  · rw [advanceCandidateState_register_frame _ _ (by decide) (by decide)]
    exact ha.active
  · rw [advanceCandidateState_register_frame _ _ (by decide) (by decide)]
    exact hl
  · change Function.update (advanceState a).stacks (tupleStacks 3) [] (tupleStacks 3) = []
    exact Function.update_self _ _ _
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact hp
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact hz

end AdvanceStorage


noncomputable def rootAscendState (a : State 40 896) : State 40 896 :=
  testParentState (clearWordsState currentHeadPorts a)

theorem rootAscendState_halt (a : State 40 896)
    (hf : a.stacks (tupleStacks 0) = []) :
    (rootAscendState a).regs controllerPorts.active = false := by
  rw [rootAscendState, testParentState_flag, clearWordsState_stacks]
  simp only [show tupleStacks 0 ∉ currentHeadPorts by decide, ite_false, hf, ne_eq,
    not_true_eq_false, decide_false]

/-- An exhausted root, including return from the sole empty tuple, clears
its current arrays and halts without attempting to pop a missing frame. -/
theorem rootAscend_eval (loadHead : Cmd 40 896) (a : State 40 896)
    (hf : a.stacks (tupleStacks 0) = []) :
    Eval (ascendWith loadHead) (clearWordsTime currentHeadPorts a + 2) a
      (rootAscendState a) := by
  have hbranch : Eval (.ite controllerPorts.active (resumeParentWith loadHead) (.base .skip))
      1 (rootAscendState a) (rootAscendState a) :=
    .ite_false (rootAscendState_halt a hf) (.base (.skip _))
  have he := (clearWords_eval currentHeadPorts a).seq
    ((testParent_eval (clearWordsState currentHeadPorts a)).seq hbranch)
  simpa only [ascendWith, leaveHeadCommand, rootAscendState, Nat.add_assoc] using he

theorem clearWordsTime_le_on (ports : List (Fin 896)) (a : State 40 896) (B : ℕ)
    (hb : ∀ i ∈ ports, (a.stacks i).length ≤ B) :
    clearWordsTime ports a ≤ ports.length * (2 * B + 3) := by
  induction ports generalizing a with
  | nil => simp [clearWordsTime]
  | cons src rest ih =>
    have hsrc := hb src (by simp)
    have hrest : ∀ i ∈ rest, ((clearState src a).stacks i).length ≤ B := by
      intro i hi
      by_cases he : i = src
      · subst i
        simp [clearState]
      · simpa [clearState, he] using hb i (by simp [hi])
    have htail := ih (clearState src a) hrest
    simp only [clearWordsTime, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Recording a representative grows only the two persistent frame banks.
The tapes cleared on descent remain bounded by their original word cap. -/
theorem descend_current_bound (a : State 40 896) (F : ℕ)
    (hp : a.stacks (tupleStacks 4) = []) (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∀ i ∈ currentHeadPorts, ((descendLevelState (retainedState a)).stacks i).length ≤ F := by
  have hwords := saveCursorState_words (recordRepresentativeState a)
  have hpayload : (retainedState a).stacks (tupleStacks 4) = [] := by
    unfold retainedState saveCursorState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide),
      pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    exact (recordRepresentativeState_words a hp).2.2
  intro i hi
  have hports : i ≠ tupleStacks 0 ∧ i ≠ tupleStacks 1 ∧
      i ≠ tupleStacks 6 ∧ i ≠ tupleStacks 9 := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [descendLevelState_outside _ _ hports.2.2.1 hports.2.2.2]
  by_cases h2 : i = tupleStacks 2
  · subst i
    rw [show (retainedState a).stacks (tupleStacks 2) = [] from hwords.1]
    simp
  · by_cases h7 : i = tupleStacks 7
    · subst i
      rw [show (retainedState a).stacks (tupleStacks 7) = [] from hwords.2.1]
      simp
    · by_cases h4 : i = tupleStacks 4
      · subst i
        rw [hpayload]
        simp
      · rw [retainedState_outside a i hports.1 hports.2.1 h2 h4 h7]
        exact hframe i

theorem probe_descend_clear_cost (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h B F : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) (hp : a.stacks (tupleStacks 4) = [])
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hpositive : 1 ≤ F)
    (hkey : AttainedSignatureProgram.Rescan.keyBound W h rows.length B ≤ F) :
    clearWordsTime currentHeadPorts
      (descendLevelState (retainedState (probePostState a out W rows h candidate))) ≤
        8 * (2 * F + 3) := by
  have hp' : (probePostState a out W rows h candidate).stacks (tupleStacks 4) = [] := by
    rw [SignatureRescanBridge.probe_stack_frame a out W rows h candidate ready hs
      _ (by decide) (by decide)]
    exact hp
  exact clearWordsTime_le_on currentHeadPorts _ F
    (descend_current_bound _ F hp'
      (probe_endpoint_bound a out W rows h B F candidate ready hs hlen hwidth hframe hpositive hkey))

/-- Descent stores only one bounded representative and cursor. Its local
prefix bound counts all caller stacks and does not use the rescan's time. -/
theorem descend_leaf_stack_bound (loadHead : Cmd 40 896) (a : State 40 896)
    (width F : ℕ) (hp : a.stacks (tupleStacks 4) = [])
    (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∀ prefixSteps intermediate,
      prefixSteps ≤ 22 * width + 32 +
        clearWordsTime currentHeadPorts (descendLevelState (retainedState a)) →
      Trace (compiled (descendWith loadHead) 0 0) prefixSteps
        (a.withPC (some (compiled (descendWith loadHead) 0 0).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        896 * F + 22 * width + 8 * (2 * F + 3) + 32 := by
  have hc := clearWordsTime_le_on currentHeadPorts _ F (descend_current_bound a F hp hframe)
  change clearWordsTime currentHeadPorts _ ≤ 8 * (2 * F + 3) at hc
  have hb := StructuredSpace.local_stack_bound (compiled (descendWith loadHead) 0 0)
    (a := a.withPC (some (compiled (descendWith loadHead) 0 0).entry))
    (steps := 22 * width + 8 * (2 * F + 3) + 32)
    (StreamResources.dataBits_le_mul _ hframe)
  intro p q hp hq i
  exact (hb p q (by omega) hq i).trans (by omega)

theorem exhausted_root_iteration (loadHead visit : Cmd 40 896)
    (a : State 40 896) (F : ℕ)
    (hl : a.regs controllerPorts.leaf = false)
    (hf : a.stacks (tupleStacks 0) = [])
    (hs : a.stacks remainingPorts.scratch = [])
    (hz : CounterPrograms.isZero (a.stacks remainingPorts.counter) = true)
    (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∃ n,
      Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a
        (rootAscendState (testAvailableState a)) ∧
      (rootAscendState (testAvailableState a)).regs controllerPorts.active = false ∧
      n + 1 ≤ 8 * (a.stacks remainingPorts.counter).length + 8 * (2 * F + 3) + 14 := by
  have hp := probe_exhausted_eval a hs hz
  have hwords := testAvailableState_stacks a hs
  have hframes : (testAvailableState a).stacks (tupleStacks 0) = [] := by rw [hwords, hf]
  have ha := rootAscend_eval loadHead (testAvailableState a) hframes
  have hav : (testAvailableState a).regs controllerPorts.available = false := by
    rw [testAvailableState_flag, hz]
    rfl
  have hc := clearWordsTime_le_on currentHeadPorts (testAvailableState a) F
    (fun i _ => by rw [hwords]; exact hframe i)
  change clearWordsTime currentHeadPorts (testAvailableState a) ≤ 8 * (2 * F + 3) at hc
  refine ⟨_, .exhausted hl hp hav ha, rootAscendState_halt _ hframes, ?_⟩
  omega

/-- Root return has a polynomial local source-prefix bound, including every
caller stack. The number of earlier DFS leaves does not appear. -/
theorem rootAscend_stack_bound (loadHead : Cmd 40 896) (a : State 40 896)
    (A B : ℕ) (ha : stackBits a.stacks ≤ A)
    (hb : ∀ i ∈ currentHeadPorts, (a.stacks i).length ≤ B) :
    ∀ prefixSteps intermediate, prefixSteps ≤ clearWordsTime currentHeadPorts a + 2 →
      Trace (compiled (ascendWith loadHead) 0 0) prefixSteps
        (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ A + 8 * (2 * B + 3) + 2 := by
  have htime := clearWordsTime_le_on currentHeadPorts a B hb
  change clearWordsTime currentHeadPorts a ≤ 8 * (2 * B + 3) at htime
  have hbound := StructuredSpace.local_stack_bound (compiled (ascendWith loadHead) 0 0)
    (a := a.withPC (some (compiled (ascendWith loadHead) 0 0).entry))
    (steps := 8 * (2 * B + 3) + 2) ha
  intro prefixSteps intermediate hp ht i
  simpa only [Nat.add_assoc] using hbound prefixSteps intermediate (by omega) ht i


noncomputable def initialClearState (a : State 40 896) : State 40 896 :=
  clearWordsState (List.ofFn tupleStacks) a

noncomputable def initialControlState (a : State 40 896) : State 40 896 :=
  initializeLevelsState (initialClearState a)

theorem initialClearState_tuple (a : State 40 896) (i : Fin 12) :
    (initialClearState a).stacks (tupleStacks i) = [] := by
  rw [initialClearState, clearWordsState_stacks,
    ite_eq_left (List.mem_ofFn.mpr ⟨i, rfl⟩)]

theorem initialClearState_source130 (a : State 40 896) :
    (initialClearState a).stacks 130 = a.stacks 130 := by
  rw [initialClearState, clearWordsState_stacks, ite_eq_right (by decide)]

theorem initialClearState_source649 (a : State 40 896) :
    (initialClearState a).stacks 649 = a.stacks 649 := by
  rw [initialClearState, clearWordsState_stacks, ite_eq_right (by decide)]

theorem initialControlState_tuple (a : State 40 896) (i : Fin 12)
    (h6 : i ≠ 6) (h9 : i ≠ 9) :
    (initialControlState a).stacks (tupleStacks i) = [] := by
  have he6 : tupleStacks i ≠ tupleStacks 6 := fun he => h6 (tupleStacks.injective he)
  have he9 : tupleStacks i ≠ tupleStacks 9 := fun he => h9 (tupleStacks.injective he)
  change (copyState 649 (tupleStacks 9)
    (copyState 130 (tupleStacks 6) (initialClearState a))).stacks (tupleStacks i) = []
  simp only [copyState, StackRoutines.copyStacks, Function.update_of_ne he9, Function.update_of_ne he6]
  exact initialClearState_tuple a i

theorem initialControlState_flags (a : State 40 896) (levels : ℕ)
    (hh : a.stacks 130 = List.replicate levels true) :
    (initialControlState a).regs controllerPorts.active = true ∧
      (initialControlState a).regs controllerPorts.leaf = decide (levels = 0) :=
  initializeLevelsState_flags (initialClearState a) levels
    ((initialClearState_source130 a).trans hh) (initialClearState_tuple a 6)

/-- A zero-head instance enters the single empty-tuple callback; it does not
halt early or skip its neutral group product. -/
theorem setup_zero_eval (loadHead : Cmd 40 896) (a : State 40 896) (base : ℕ)
    (hh : a.stacks 130 = []) (hz : a.stacks 649 = List.replicate base true) :
    Eval (setupWith loadHead)
      (clearWordsTime (List.ofFn tupleStacks) a + 7 * base + 14) a (initialControlState a) := by
  have hi := initializeLevels_eval (initialClearState a) (initialClearState_tuple a 5)
  rw [initialClearState_source130, initialClearState_source649, hh, hz] at hi
  simp only [List.length_nil, List.length_replicate, Nat.mul_zero, Nat.zero_add] at hi
  have hleaf := (initialControlState_flags a 0 hh).2
  have hbranch : Eval (.ite controllerPorts.leaf (.base .skip)
      (.seq loadHead resetGeneratorCommand)) 1 (initialControlState a) (initialControlState a) :=
    .ite_true hleaf (.base (.skip _))
  have he := (clearWords_eval (List.ofFn tupleStacks) a).seq (hi.seq hbranch)
  simpa only [setupWith, initialClearState, initialControlState, Nat.add_assoc] using he

section InitialStorage

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem initial_ancestor_storage (levels base : ℕ)
    (ancestors : Prefix (Representatives key) 0) (a : State 40 896)
    (hh : a.stacks 130 = List.replicate levels true)
    (hz : a.stacks 649 = List.replicate base true) :
    AncestorStorage h key levels base 0 ancestors (initialControlState a) := by
  have hw := initializeLevelsState_words (initialClearState a) levels base
    ((initialClearState_source130 a).trans hh) ((initialClearState_source649 a).trans hz)
    (initialClearState_tuple a 6) (initialClearState_tuple a 9)
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, (initialControlState_flags a levels hh).1⟩
  · rw [initialControlState_tuple _ _ (by decide) (by decide)]
    simp [cursorFrames]
  · rw [initialControlState_tuple _ _ (by decide) (by decide)]
    simp [representativeFrames, representativeWords, suspendedFrames]
  · simpa only [initialControlState, Nat.sub_zero] using hw.1
  · simpa only [initialControlState, Nat.add_zero] using hw.2

theorem initial_leaf_storage (base : ℕ)
    (ancestors : Prefix (Representatives key) 0) (a : State 40 896)
    (hh : a.stacks 130 = []) (hz : a.stacks 649 = List.replicate base true) :
    LeafStorage h key 0 base ancestors (initialControlState a) := by
  refine ⟨initial_ancestor_storage h key 0 base ancestors a hh hz,
    (initialControlState_flags a 0 hh).2, ?_⟩
  intro i hi
  simp only [currentHeadPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact initialControlState_tuple a _ (by decide) (by decide)

end InitialStorage


/-- The presence test does not change any stack, and cleanup leaves both
persistent prefix banks intact. -/
theorem checkedReturnState_stack (a : State 40 896) (i : Fin 896) :
    (rootAscendState a).stacks i = if i ∈ currentHeadPorts then [] else a.stacks i :=
  clearWordsState_stacks currentHeadPorts a i

section ParentReturn

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem cursorFrames_nonempty (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) :
    cursorFrames h key (depth + 1) ancestors ≠ [] := by
  intro he
  have hl := congrArg List.length he
  rw [cursorFrames_pop, List.length_append, cursorFrame_length, List.length_nil] at hl
  omega

theorem checkedReturnState_active (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) ancestors) :
    (rootAscendState a).regs controllerPorts.active = true := by
  rw [rootAscendState, testParentState_flag, clearWordsState_stacks,
    ite_eq_right (by decide), hf]
  exact decide_eq_true (cursorFrames_nonempty h key depth ancestors)

noncomputable def parentWordsState (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) : State 40 896 :=
  restoreCursorState
    (dropRepresentativeState (rootAscendState a)
      (ExecCNFTupleEnumeration.fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
      (representativeFrames h key depth (Fin.init ancestors)))
    (ExecCNFTupleEnumeration.fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (ExecCNFTupleEnumeration.fixedBits (h depth + 1)
      (2 ^ h depth - (ancestors (Fin.last depth)).val.val))
    (cursorFrames h key depth (Fin.init ancestors))

noncomputable def parentReturnState (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) : State 40 896 :=
  ascendLevelState (parentWordsState h key depth ancestors a)

/-- Restore the attained parent's saved bounded candidate and fuel without
rescanning any earlier candidate. The matrix reload follows this prefix. -/
theorem parent_return_prefix_eval (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) ancestors)
    (hr : a.stacks (tupleStacks 1) = representativeFrames h key (depth + 1) ancestors) :
    Eval (.seq dropRepresentativeCommand (.seq restoreCursorCommand ascendLevelCommand))
      (20 * h depth + 25) (rootAscendState a) (parentReturnState h key depth ancestors a) := by
  have he := returnFrames_eval h key depth ancestors (rootAscendState a)
    (by rw [checkedReturnState_stack, ite_eq_right (by decide), hf])
    (by rw [checkedReturnState_stack, ite_eq_right (by decide), hr])
    (by rw [checkedReturnState_stack, ite_eq_left (by decide)])
    (by rw [checkedReturnState_stack, ite_eq_left (by decide)])
    (by rw [checkedReturnState_stack, ite_eq_left (by decide)])
  have hall := seq_reassociate (he.seq (ascendLevel_eval (parentWordsState h key depth ancestors a)))
  change Eval _ _ (rootAscendState a) (parentReturnState h key depth ancestors a) at hall
  convert hall using 1

theorem parentWordsState_fields (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) :
    (parentWordsState h key depth ancestors a).stacks (tupleStacks 0) =
        cursorFrames h key depth (Fin.init ancestors) ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 1) =
        representativeFrames h key depth (Fin.init ancestors) ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 2) =
        ExecCNFTupleEnumeration.fixedBits (h depth) (ancestors (Fin.last depth)).val.val ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 7) =
        ExecCNFTupleEnumeration.fixedBits (h depth + 1)
          (2 ^ h depth - (ancestors (Fin.last depth)).val.val) ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 4) = [] :=
  returnFrames_state h key depth ancestors (rootAscendState a)


theorem parentWordsState_outside (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) (i : Fin 896)
    (h0 : i ≠ tupleStacks 0) (h1 : i ≠ tupleStacks 1) (h2 : i ≠ tupleStacks 2)
    (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (parentWordsState h key depth ancestors a).stacks i = (rootAscendState a).stacks i := by
  unfold parentWordsState restoreCursorState
  rw [popWordState_outside _ _ _ _ _ _ _ h0 h2,
    popWordState_outside _ _ _ _ _ _ _ h0 h7]
  change Function.update (popWordState _ _ _ _ _ _).stacks (tupleStacks 4) [] i = _
  rw [Function.update_of_ne h4, popWordState_outside _ _ _ _ _ _ _ h1 h4]

theorem parentWordsState_register (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (parentWordsState h key depth ancestors a).regs j = (rootAscendState a).regs j := by
  unfold parentWordsState restoreCursorState
  rw [popWordState_register_frame _ _ _ _ _ _ j h0 h1,
    popWordState_register_frame _ _ _ _ _ _ j h0 h1]
  change readRegs (popWordState _ _ _ _ _ _).regs 0 1 none j = _
  rw [StackRoutines.readRegs_frame _ _ _ _ _ h0 h1,
    popWordState_register_frame _ _ _ _ _ _ j h0 h1]

theorem ascendLevelState_outside (a : State 40 896) (i : Fin 896)
    (h6 : i ≠ tupleStacks 6) (h9 : i ≠ tupleStacks 9) :
    (ascendLevelState a).stacks i = a.stacks i := by
  simp [ascendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, h6, h9]

theorem ascendLevelState_active (a : State 40 896) :
    (ascendLevelState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  simp [ascendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, readRegs,
    controllerPorts]

/-- The parent address and unary remaining-head word are reconstructed by
one paid ascent; no saved matrix or whole assignment table is retained. -/
theorem parent_return_ancestor_storage (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (ha : AncestorStorage h key levels base (depth + 1) ancestors a) :
    AncestorStorage h key levels base depth (Fin.init ancestors)
      (parentReturnState h key depth ancestors a) := by
  have hf := parentWordsState_fields h key depth ancestors a
  have hh : (parentWordsState h key depth ancestors a).stacks (tupleStacks 6) =
      List.replicate (levels - (depth + 1)) true := by
    rw [parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_right (by decide)]
    exact ha.heads
  have hz : (parentWordsState h key depth ancestors a).stacks (tupleStacks 9) =
      List.replicate (base + depth + 1) true := by
    rw [parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_right (by decide), ha.address]
    simp [Nat.add_assoc]
  have hl := ascendLevelState_words (parentWordsState h key depth ancestors a)
    (levels - (depth + 1)) (base + depth) hh hz
  refine ⟨by have := ha.depth_le; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.1
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.1
  · rw [parentReturnState, hl.1]
    have hd := ha.depth_le
    congr 1
    omega
  · exact hl.2.1
  · rw [parentReturnState, ascendLevelState_active,
      parentWordsState_register _ _ _ _ _ _ (by decide) (by decide)]
    exact checkedReturnState_active h key depth ancestors a ha.cursors

theorem parent_return_cursor (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) :
    CursorWords (parentReturnState h key depth ancestors a) (h depth)
      (ancestors (Fin.last depth)).val.val := by
  have hf := parentWordsState_fields h key depth ancestors a
  have hcan : (parentReturnState h key depth ancestors a).stacks candidatePorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h depth) (ancestors (Fin.last depth)).val.val := by
    rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.2.1
  have hrem : (parentReturnState h key depth ancestors a).stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h depth + 1)
        (2 ^ h depth - (ancestors (Fin.last depth)).val.val) := by
    rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.2.2.1
  refine ⟨(ancestors (Fin.last depth)).val.isLt.le, ?_, ?_, fun _ => hcan, hrem, ?_, ?_⟩
  · rw [hcan]
    exact ExecCNFTupleEnumeration.fixedBits_value _ _ (ancestors (Fin.last depth)).val.isLt
  · rw [hcan, ExecCNFTupleEnumeration.fixedBits_length]
    omega
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide),
      parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_left (by decide)]
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide),
      parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_left (by decide)]

end ParentReturn


section DuplicateIteration

open SignatureRescanBridge

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- A losing signature candidate executes the full native predicate and one
bounded advance. No matrix reload or fresh generator is invoked. -/
theorem duplicate_iteration (loadHead visit : Cmd 40 896)
    (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val)
    (candidate : Fin (2 ^ h depth.val)) (a : State 40 896)
    (W : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (ha : ScanStorage h key levels base depth ancestors candidate.val a)
    (ready : CandidateReady a W rows (h depth.val) candidate)
    (hlen : ∀ row ∈ rows, row.length = h depth.val)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hkernel : ∀ i j : Fin (2 ^ h depth.val),
      AttainedSignatureProgram.Rescan.naturalKey W rows (h depth.val) i =
        AttainedSignatureProgram.Rescan.naturalKey W rows (h depth.val) j ↔
      key depth.val i = key depth.val j)
    (hdup : ¬ ∀ j, j < candidate → key depth.val j ≠ key depth.val candidate) :
    ∃ n out,
      Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a
        (advanceCandidateState (probePostState a out W rows (h depth.val) candidate)) ∧
      ScanStorage h key levels base depth ancestors (candidate.val + 1)
        (advanceCandidateState (probePostState a out W rows (h depth.val) candidate)) ∧
      n + 1 ≤ (candidate.val + 1) *
        (AttainedSignatureProgram.Rescan.polynomialBudget W rows (h depth.val) B +
          32 * h depth.val + 2 * (a.stacks (rescanStacks 22)).length +
          2 * AttainedSignatureProgram.Rescan.keyBound W (h depth.val) rows.length B + 71) := by
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false := by
    rw [ha.toCursorWords.available]
    simp only [Nat.ne_of_lt candidate.isLt, decide_false]
  obtain ⟨np, hnp, out, hprobe⟩ := probe_ready_eval a W rows (h depth.val) B hlen hwidth
    candidate ready ha.decrementScratch hzero
  let b := probePostState a out W rows (h depth.val) candidate
  have hbwords : CursorWords b (h depth.val) candidate.val :=
    probe_preserves_cursor a out W rows (h depth.val) candidate ready ha.toCursorWords
  have hflags := probe_control_flags a out W rows (h depth.val) candidate hzero
  have hframe (i : Fin 896) (hk : i ≠ rescanStacks 17) (hl : i ≠ rescanStacks 22) :
      b.stacks i = a.stacks i :=
    probe_stack_frame a out W rows (h depth.val) candidate ready ha.decrementScratch i hk hl
  have hbanc : AncestorStorage h key levels base depth.val ancestors b := by
    refine ⟨ha.depth_le, ?_, ?_, ?_, ?_, hflags.1.trans ha.active⟩
    · rw [hframe _ (by decide) (by decide)]; exact ha.cursors
    · rw [hframe _ (by decide) (by decide)]; exact ha.representatives
    · rw [hframe _ (by decide) (by decide)]; exact ha.heads
    · rw [hframe _ (by decide) (by decide)]; exact ha.address
  have hbfresh : b.regs controllerPorts.fresh = false := by
    rw [hflags.2.2.2]
    exact (actual_duplicate_iff_model _ _ hkernel candidate).mpr hdup
  have hnext := advance_scan_storage h key levels base depth ancestors candidate.val b
    hbanc hbwords candidate.isLt (hflags.2.1.trans ha.leaf)
    ((hframe _ (by decide) (by decide)).trans ha.payload)
    ((hframe _ (by decide) (by decide)).trans ha.predecessor)
  have hadv := advanceCandidate_eval b hbwords.incrementScratch hbwords.decrementScratch
  have hi : Iteration controllerPorts (assembleRoutines loadHead candidateCall visit)
      (np + (advanceTime b + 2 * (b.stacks (tupleStacks 3)).length + 3) + 3) a
      (advanceCandidateState b) :=
    .duplicate ha.leaf hprobe hflags.2.2.1 hbfresh hadv
  refine ⟨_, out, hi, hnext, ?_⟩
  have hpos : 0 < CounterPrograms.value (b.stacks remainingPorts.counter) := by
    rw [hbwords.remaining_value]
    have hc := candidate.isLt
    omega
  have hat := advanceTime_le b hpos
  rw [hbwords.exact candidate.isLt, hbwords.remaining] at hat
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at hat
  have hkey : b.stacks (tupleStacks 3) =
      AttainedSignatureProgram.Rescan.naturalKey W rows (h depth.val) candidate := by
    rw [show b.stacks = _ from probe_stacks a out W rows (h depth.val) candidate ready ha.decrementScratch]
    rw [Function.update_of_ne (by decide : tupleStacks 3 ≠ rescanStacks 22)]
    exact Function.update_self _ _ _
  have hk := AttainedSignatureProgram.Rescan.naturalKey_length_le W rows (h depth.val) B
    hlen hwidth candidate
  rw [← hkey] at hk
  have hrem := congrArg List.length ha.remaining
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at hrem
  let extra := 32 * h depth.val + 2 * (a.stacks (rescanStacks 22)).length +
    2 * AttainedSignatureProgram.Rescan.keyBound W (h depth.val) rows.length B + 71
  have hmul : extra ≤ (candidate.val + 1) * extra := by
    have hm := Nat.mul_le_mul_right extra (show 1 ≤ candidate.val + 1 by omega)
    simpa only [one_mul] using hm
  calc
    _ ≤ (candidate.val + 1) *
        AttainedSignatureProgram.Rescan.polynomialBudget W rows (h depth.val) B + extra := by
      dsimp only [extra]
      simp only [rescanStacks_fresh] at hnp ⊢
      omega
    _ ≤ (candidate.val + 1) *
        AttainedSignatureProgram.Rescan.polynomialBudget W rows (h depth.val) B +
        (candidate.val + 1) * extra := Nat.add_le_add_left hmul _
    _ = _ := by dsimp [extra]; ring

end DuplicateIteration


/-- Current-head cleanup does not erase the newly attained child prefix or
its unary depth/address words. This also covers internal children. -/
theorem descend_ancestor_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (a : State 40 896) (hd : depth < levels)
    (ha : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val) (hp : a.stacks (tupleStacks 4) = []) :
    AncestorStorage h key levels base (depth + 1) (Fin.snoc ancestors rep) (descendClearState a) := by
  have hf := retainFrames_state h key depth ancestors rep a
    ha.cursors ha.representatives (hw.exact rep.val.isLt) hw.remaining hp
  have heq : levels - depth = levels - (depth + 1) + 1 := by omega
  have hr : (retainedState a).stacks (tupleStacks 6) =
      List.replicate (levels - (depth + 1) + 1) true := by
    rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      ha.heads, heq]
  have hz : (retainedState a).stacks (tupleStacks 9) = List.replicate (base + depth) true := by
    rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ha.address
  have hl := descendLevelState_words (retainedState a) (levels - (depth + 1)) (base + depth) hr hz
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.1
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.1
  · rw [descendClearState_stack _ _ (by decide), hl.1]
  · rw [descendClearState_stack _ _ (by decide), hl.2.1]
    simp [Nat.add_assoc]
  · rw [descendClearState_active]
    exact ha.active

theorem resetState_outside (a : State 40 896) (i : Fin 896)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (resetState a).stacks i = a.stacks i := by
  change (initialFuelState (copyState 651 (tupleStacks 4)
    (copyState 651 (tupleStacks 2) a))).stacks i = a.stacks i
  unfold initialFuelState
  rw [CounterForPrograms.install_other_stack initialFuelPorts _ _ _ _ _ _ i h4 h7]
  simp only [copyState, StackRoutines.copyStacks, Function.update_of_ne h4, Function.update_of_ne h2]

theorem resetGeneratorState_outside (a : State 40 896) (i : Fin 896)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7)
    (h8 : i ≠ tupleStacks 8) :
    (resetGeneratorState a).stacks i = a.stacks i := by
  change Function.update (resetState a).stacks (tupleStacks 8)
    ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) i = a.stacks i
  rw [Function.update_of_ne h8, resetState_outside a i h2 h4 h7]

theorem resetGeneratorState_cursor (a : State 40 896) (width : ℕ)
    (hh : a.stacks 651 = List.replicate width false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = [])
    (ht : a.stacks (tupleStacks 5) = []) (hi : a.stacks (tupleStacks 10) = []) :
    CursorWords (resetGeneratorState a) width 0 := by
  have hwords := resetState_words a width hh hc hp
  have hcandidate : (resetGeneratorState a).stacks candidatePorts.counter =
      ExecCNFTupleEnumeration.fixedBits width 0 := by
    change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) candidatePorts.counter = _
    rw [Function.update_of_ne (by decide)]
    exact resetState_assignment a width hh hc hp
  have hremaining : (resetGeneratorState a).stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (width + 1) (2 ^ width) := by
    change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) remainingPorts.counter = _
    rw [Function.update_of_ne (by decide)]
    exact hwords.2.1.trans (initial_remaining_word width)
  refine ⟨Nat.zero_le _, ?_, ?_, fun _ => hcandidate, ?_, ?_, ?_⟩
  · rw [hcandidate, ExecCNFTupleEnumeration.fixedBits_value _ _ (Nat.pow_pos (by decide))]
  · rw [hcandidate, ExecCNFTupleEnumeration.fixedBits_length]
    omega
  · simpa using hremaining
  · rw [resetGeneratorState_outside _ _ (by decide) (by decide) (by decide) (by decide)]
    exact hi
  · rw [resetGeneratorState_outside _ _ (by decide) (by decide) (by decide) (by decide)]
    exact ht

theorem resetGeneratorState_predecessor (a : State 40 896) (width : ℕ)
    (hh : a.stacks 651 = List.replicate width false)
    (hp : a.stacks (tupleStacks 8) = []) :
    (resetGeneratorState a).stacks (tupleStacks 8) = List.replicate width false := by
  change Function.update (resetState a).stacks (tupleStacks 8)
    ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) (tupleStacks 8) = _
  rw [Function.update_self, resetState_source,
    resetState_outside _ _ (by decide) (by decide) (by decide), hh, hp, List.append_nil]

theorem resetGeneratorState_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (hav : j ≠ controllerPorts.available)
    (hfresh : j ≠ controllerPorts.fresh) :
    (resetGeneratorState a).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro he; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro he; subst j; norm_num at hj
  change readRegs (resetState a).regs 0 1 none j = a.regs j
  rw [StackRoutines.readRegs_frame _ _ _ _ _ h0 h1]
  unfold resetState
  simp only [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    Function.update_of_ne hfresh, Function.update_of_ne hav]
  unfold initialFuelState
  rw [counter_install_register_frame _ _ _ _ _ _ _ j ?_]
  · exact (StackRoutines.readRegs_frame _ _ _ _ _ h0 h1).trans
      (StackRoutines.readRegs_frame _ _ _ _ _ h0 h1)
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    have hil := i.isLt
    change i.val = j.val at hv
    omega

/-- Reset follows a real matrix load. It preserves the attained ancestor
frames and prepares exactly the first numeric assignment for this head. -/
theorem reset_scan_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (a : State 40 896)
    (ha : AncestorStorage h key levels base depth.val ancestors a)
    (hl : a.regs controllerPorts.leaf = false)
    (hh : a.stacks 651 = List.replicate (h depth.val) false)
    (hc : a.stacks (tupleStacks 2) = []) (hk : a.stacks (tupleStacks 3) = [])
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hz : a.stacks (tupleStacks 8) = []) (hi : a.stacks (tupleStacks 10) = []) :
    ScanStorage h key levels base depth ancestors 0 (resetGeneratorState a) := by
  have hf (i : Fin 896) (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4)
      (h7 : i ≠ tupleStacks 7) (h8 : i ≠ tupleStacks 8) :
      (resetGeneratorState a).stacks i = a.stacks i :=
    resetGeneratorState_outside a i h2 h4 h7 h8
  refine ⟨⟨ha.depth_le, ?_, ?_, ?_, ?_, ?_⟩,
    resetGeneratorState_cursor a (h depth.val) hh hc hp ht hi, ?_, ?_, ?_,
    resetGeneratorState_predecessor a (h depth.val) hh hz⟩
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.cursors
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.representatives
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.heads
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.address
  · rw [resetGeneratorState_register_frame _ _ (by decide) (by decide) (by decide)]
    exact ha.active
  · rw [resetGeneratorState_register_frame _ _ (by decide) (by decide) (by decide)]
    exact hl
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact hk
  · change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) (tupleStacks 4) = []
    rw [Function.update_of_ne (by decide)]
    exact (resetState_words a (h depth.val) hh hc hp).2.2

/-- Composition for an internal descent uses the supplied actual loader
evaluation, then the concrete power-of-two cursor initializer. -/
theorem descend_internal_eval (loadHead : Cmd 40 896) (a loaded : State 40 896)
    (width candidate childWidth loadSteps : ℕ)
    (hc : a.stacks (tupleStacks 2) = ExecCNFTupleEnumeration.fixedBits width candidate)
    (hn : a.stacks (tupleStacks 7) =
      ExecCNFTupleEnumeration.fixedBits (width + 1) (2 ^ width - candidate))
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hl : (descendClearState a).regs controllerPorts.leaf = false)
    (hload : Eval loadHead loadSteps (descendClearState a) loaded)
    (hwidth : loaded.stacks 651 = List.replicate childWidth false)
    (hremaining : loaded.stacks (tupleStacks 7) = [])
    (hscratch : loaded.stacks (tupleStacks 5) = [])
    (hpayload : loaded.stacks (tupleStacks 4) = []) :
    Eval (descendWith loadHead)
      (22 * width + 25 * childWidth + loadSteps +
        clearWordsTime currentHeadPorts (descendLevelState (retainedState a)) + 53)
      a (resetGeneratorState loaded) := by
  have hf := retainFrames_eval width candidate a hc hn hp ht
  have hreset := resetGenerator_eval loaded childWidth hwidth hremaining hscratch hpayload
  have hbranch : Eval (.ite controllerPorts.leaf (.base .skip)
      (.seq loadHead resetGeneratorCommand)) (loadSteps + (25 * childWidth + 22) + 1)
      (descendClearState a) (resetGeneratorState loaded) := .ite_false hl (hload.seq hreset)
  generalize hcost : 22 * width + 25 = frameSteps at hf
  cases hf with
  | seq hrecord hsave =>
    have hall := hrecord.seq (hsave.seq ((descendLevel_eval (retainedState a)).seq
      ((clearWords_eval currentHeadPorts (descendLevelState (retainedState a))).seq hbranch)))
    change Eval (descendWith loadHead) _ a (resetGeneratorState loaded) at hall
    convert hall using 1
    omega

theorem descend_internal_leaf_flag (a : State 40 896) (remaining address : ℕ)
    (hpositive : 0 < remaining)
    (hh : a.stacks (tupleStacks 6) = List.replicate (remaining + 1) true)
    (hz : a.stacks (tupleStacks 9) = List.replicate address true) :
    (descendClearState a).regs controllerPorts.leaf = false := by
  have hw := descendLevelState_words (retainedState a) remaining address
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hh)
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz)
  rw [descendClearState, clearWordsState_register_frame _ _ _ (by decide) (by decide), hw.2.2]
  simp only [Nat.ne_of_gt hpositive, decide_false]

section LeafStorage

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem descend_leaf_storage (depth base : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (a : State 40 896)
    (ha : AncestorStorage h key (depth + 1) base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val)
    (hp : a.stacks (tupleStacks 4) = []) :
    LeafStorage h key (depth + 1) base (Fin.snoc ancestors rep) (descendClearState a) := by
  have hf := retainFrames_state h key depth ancestors rep a
    ha.cursors ha.representatives (hw.exact rep.val.isLt) hw.remaining hp
  have hr : a.stacks (tupleStacks 6) = [true] := by simpa using ha.heads
  have hl := descendLevelState_words (retainedState a) 0 (base + depth)
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr)
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ha.address)
  refine ⟨⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩, descendClearState_leaf a (base + depth) hr ha.address,
    descendClearState_cleared a⟩
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.1
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.1
  · rw [descendClearState_stack _ _ (by decide), hl.1]
    simp
  · rw [descendClearState_stack _ _ (by decide), hl.2.1]
    simp [Nat.add_assoc]
  · rw [descendClearState_active]
    exact ha.active

end LeafStorage

theorem leaf_tuple_bound (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base hmax : ℕ)
    (ancestors : Prefix (Representatives key) levels) (a : State 40 896)
    (ha : LeafStorage h key levels base ancestors a) (hh : ∀ d < levels, h d ≤ hmax) :
    ∀ i : Fin 12, (a.stacks (tupleStacks i)).length ≤
      6 * levels * (hmax + 1) + (base + levels) := by
  have hf := ha.toAncestorStorage.frame_bound h key hmax hh
  intro i
  fin_cases i
  · change (a.stacks (tupleStacks 0)).length ≤ _
    omega
  · change (a.stacks (tupleStacks 1)).length ≤ _
    omega
  · change (a.stacks (tupleStacks 2)).length ≤ _
    rw [ha.cleared _ (by decide)]
    simp
  · change (a.stacks (tupleStacks 3)).length ≤ _
    rw [ha.cleared _ (by decide)]
    simp
  · change (a.stacks (tupleStacks 4)).length ≤ _
    rw [ha.cleared _ (by decide)]
    simp
  · change (a.stacks (tupleStacks 5)).length ≤ _
    rw [ha.cleared _ (by decide)]
    simp
  · change (a.stacks (tupleStacks 6)).length ≤ _
    rw [ha.heads]
    simp
  · change (a.stacks (tupleStacks 7)).length ≤ _
    rw [ha.cleared _ (by decide)]
    simp
  · change (a.stacks (tupleStacks 8)).length ≤ _
    rw [ha.cleared _ (by decide)]
    simp
  · change (a.stacks (tupleStacks 9)).length ≤ _
    rw [ha.address, List.length_replicate]
    omega
  · change (a.stacks (tupleStacks 10)).length ≤ _
    rw [ha.cleared _ (by decide)]
    simp
  · change (a.stacks (tupleStacks 11)).length ≤ _
    rw [ha.cleared _ (by decide)]
    simp

theorem descendClearState_outside_tuple (a : State 40 896) (i : Fin 896)
    (hi : ∀ j : Fin 12, i ≠ tupleStacks j) : (descendClearState a).stacks i = a.stacks i := by
  have hc : i ∉ currentHeadPorts := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨hi 2, hi 3, hi 4, hi 5, hi 7, hi 8, hi 10, hi 11⟩
  rw [descendClearState_stack a i hc, descendLevelState_outside _ _ (hi 6) (hi 9),
    retainedState_outside _ _ (hi 0) (hi 1) (hi 2) (hi 4) (hi 7)]

/-- The larger transient descent bound is discharged at the next leaf
boundary using the global attained-prefix frame cap. -/
theorem descend_leaf_endpoint_bound (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base hmax F : ℕ)
    (ancestors : Prefix (Representatives key) levels) (a : State 40 896)
    (ha : LeafStorage h key levels base ancestors (descendClearState a))
    (hh : ∀ d < levels, h d ≤ hmax)
    (hcap : 6 * levels * (hmax + 1) + (base + levels) ≤ F)
    (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∀ i, ((descendClearState a).stacks i).length ≤ F := by
  intro i
  by_cases ht : ∃ j : Fin 12, i = tupleStacks j
  · obtain ⟨j, rfl⟩ := ht
    exact (leaf_tuple_bound h key levels base hmax ancestors _ ha hh j).trans hcap
  · rw [descendClearState_outside_tuple a i (fun j hj => ht ⟨j, hj⟩)]
    exact hframe i

/-- A fresh signature at the final head executes the full actual rescan,
saves its attained representative, and reaches the cleaned visitor boundary. -/
theorem fresh_leaf_iteration (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d)
    (loadHead visit : Cmd 40 896) (depth base : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (a : State 40 896) (W : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (ha : ScanStorage h key (depth + 1) base (Fin.last depth) ancestors rep.val.val a)
    (ready : CandidateReady a W rows (h depth) rep.val)
    (hlen : ∀ row ∈ rows, row.length = h depth)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hkernel : ∀ i j : Fin (2 ^ h depth),
      AttainedSignatureProgram.Rescan.naturalKey W rows (h depth) i =
        AttainedSignatureProgram.Rescan.naturalKey W rows (h depth) j ↔
      key depth i = key depth j) :
    ∃ n out,
      Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a
        (descendClearState (probePostState a out W rows (h depth) rep.val)) ∧
      LeafStorage h key (depth + 1) base (Fin.snoc ancestors rep)
        (descendClearState (probePostState a out W rows (h depth) rep.val)) ∧
      n + 1 ≤ (rep.val.val + 1) * AttainedSignatureProgram.Rescan.polynomialBudget W rows (h depth) B +
        8 * (a.stacks remainingPorts.counter).length + 2 * (a.stacks (rescanStacks 22)).length +
        22 * h depth + clearWordsTime currentHeadPorts
          (descendLevelState (retainedState (probePostState a out W rows (h depth) rep.val))) + 51 := by
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false := by
    rw [ha.toCursorWords.available]
    simp only [Fin.val_last, Nat.ne_of_lt rep.val.isLt, decide_false]
  obtain ⟨np, hnp, out, he⟩ := probe_ready_eval a W rows (h depth) B hlen hwidth
    rep.val ready ha.decrementScratch hzero
  let b := probePostState a out W rows (h depth) rep.val
  have hw : CursorWords b (h depth) rep.val.val :=
    SignatureRescanBridge.probe_preserves_cursor a out W rows (h depth) rep.val ready ha.toCursorWords
  have hflags := SignatureRescanBridge.probe_control_flags a out W rows (h depth) rep.val hzero
  have hf (i : Fin 896) (hk : i ≠ rescanStacks 17) (hl : i ≠ rescanStacks 22) :
      b.stacks i = a.stacks i :=
    SignatureRescanBridge.probe_stack_frame a out W rows (h depth) rep.val ready
      ha.decrementScratch i hk hl
  have hb : AncestorStorage h key (depth + 1) base depth ancestors b := by
    refine ⟨ha.depth_le, ?_, ?_, ?_, ?_, hflags.1.trans ha.active⟩
    · rw [hf _ (by decide) (by decide)]; exact ha.cursors
    · rw [hf _ (by decide) (by decide)]; exact ha.representatives
    · rw [hf _ (by decide) (by decide)]; exact ha.heads
    · rw [hf _ (by decide) (by decide)]; exact ha.address
  have hp : b.stacks (tupleStacks 4) = [] := by
    rw [hf _ (by decide) (by decide)]; exact ha.payload
  have hr : b.stacks (tupleStacks 6) = [true] := by simpa using hb.heads
  have hdesc := descend_leaf_eval loadHead b (h depth) rep.val.val (base + depth)
    (hw.exact rep.val.isLt) hw.remaining hp hw.decrementScratch hr hb.address
  have hbfresh : b.regs controllerPorts.fresh = true := by
    rw [hflags.2.2.2]
    exact (actual_fresh_iff_model _ _ hkernel rep.val).mpr rep.property
  refine ⟨_, out, .fresh ha.leaf he hflags.2.2.1 hbfresh hdesc,
    descend_leaf_storage h key depth base ancestors rep b hb hw hp, ?_⟩
  dsimp only [b] at *
  omega

/-- One losing candidate has a joint actual run, polynomial all-stack
prefix bound, and the unchanged fixed boundary bound. The exponential
candidate value occurs only in the time estimate. -/
theorem duplicate_run_space (loadHead visit : Cmd 40 896) (a : State 40 896)
    (W : List Bool) (rows : List (List (List Bool))) (h B F : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hw : CursorWords a h candidate.val)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hleaf : a.regs controllerPorts.leaf = false)
    (hdup : Bool.not (AttainedSignatures.duplicateScan
      (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate) = false)
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hpositive : 1 ≤ F) (hcursor : h + 1 ≤ F)
    (hkey : AttainedSignatureProgram.Rescan.keyBound W h rows.length B ≤ F)
    (hspace : AttainedSignatureProgram.Rescan.spaceBudget W rows h B ≤ F) :
    ∃ n out,
      Eval (body controllerPorts (assembleRoutines loadHead candidateCall visit)) n a
        (advanceCandidateState (probePostState a out W rows h candidate)) ∧
      (∀ i, ((advanceCandidateState (probePostState a out W rows h candidate)).stacks i).length ≤ F) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
          prefixSteps (a.withPC (some (compiled
            (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1)) ∧
      n + 1 ≤ (candidate.val + 1) *
        (AttainedSignatureProgram.Rescan.polynomialBudget W rows h B + 64 * F + 100) := by
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false := by
    rw [hw.available]
    simp only [Nat.ne_of_lt candidate.isLt, decide_false]
  obtain ⟨np, hnp, out, hp, hpSpace⟩ := SignatureRescanBridge.probe_run_space
    a W rows h B F hlen hwidth candidate ready hw.decrementScratch hzero hframe
  let b := probePostState a out W rows h candidate
  let c := advanceCandidateState b
  have hb := probe_endpoint_bound a out W rows h B F candidate ready hw.decrementScratch
    hlen hwidth hframe hpositive hkey
  have hwords := SignatureRescanBridge.probe_preserves_cursor a out W rows h candidate ready hw
  have hflags := SignatureRescanBridge.probe_control_flags a out W rows h candidate hzero
  have hfresh : b.regs controllerPorts.fresh = false := hflags.2.2.2.trans hdup
  have ha : Eval advanceCandidateCommand
      (advanceTime b + 2 * (b.stacks (tupleStacks 3)).length + 3) b c :=
    advanceCandidate_eval b hwords.incrementScratch hwords.decrementScratch
  let na := advanceTime b + 2 * (b.stacks (tupleStacks 3)).length + 3
  have hpos : 0 < CounterPrograms.value (b.stacks remainingPorts.counter) := by
    rw [hwords.remaining_value]
    have hc := candidate.isLt
    omega
  have htime := advanceTime_le b hpos
  rw [hwords.exact candidate.isLt, hwords.remaining] at htime
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at htime
  have hna : na ≤ 26 * F + 27 := by
    have hk := hb (tupleStacks 3)
    dsimp only [na, b] at *
    omega
  have hps : ∀ p q, p ≤ np → Trace (compiled (probeWith candidateCall) 0 0) p
      (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ 2000 * (F + 1) := by
    intro p q hpn hq i
    have hs := hpSpace p q (by omega) hq i
    have hr := hframe remainingPorts.counter
    have hf := hframe (rescanStacks 22)
    omega
  have has : ∀ p q, p ≤ na → Trace (compiled advanceCandidateCommand 0 0) p
      (b.withPC (some (compiled advanceCandidateCommand 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ 2000 * (F + 1) := by
    have hh := StructuredSpace.local_stack_bound (compiled advanceCandidateCommand 0 0)
      (a := b.withPC (some (compiled advanceCandidateCommand 0 0).entry)) (steps := na)
      (StreamResources.dataBits_le_mul _ hb)
    intro p q hpn hq i
    exact (hh p q hpn hq i).trans (by omega)
  let freshBranch : Cmd 40 896 := .ite controllerPorts.fresh (descendWith loadHead) advanceCandidateCommand
  let availableBranch : Cmd 40 896 := .ite controllerPorts.available freshBranch (ascendWith loadHead)
  have hfe : Eval freshBranch (na + 1) b c := .ite_false hfresh ha
  have hfs := StructuredSpace.conditional_false_stack_bound
    (yes := descendWith loadHead) hfresh ha 0 0 has
    (compiled freshBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have haveval : Eval availableBranch (na + 1 + 1) b c := .ite_true hflags.2.2.1 hfe
  have havspace := StructuredSpace.conditional_true_stack_bound
    (no := ascendWith loadHead) hflags.2.2.1 hfe 0 0 hfs
    (compiled availableBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hseq := hp.seq haveval
  have hsseq := StructuredSpace.sequence_stack_bound hp haveval 0 0 hps havspace
    (compiled (.seq (probeWith candidateCall) availableBranch) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have he : Eval (body controllerPorts (assembleRoutines loadHead candidateCall visit))
      (np + (na + 1 + 1) + 1) a c := .ite_false hleaf hseq
  have hwhole := StructuredSpace.conditional_false_stack_bound
    (yes := .seq visit (ascendWith loadHead)) hleaf hseq 0 0 hsseq
    (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  refine ⟨_, out, he,
    advance_endpoint_bound b h candidate F hwords candidate.isLt hb hcursor,
    StructuredSpace.compiled_halt_stack_bound he 0 0 hwhole, ?_⟩
  have hr := hframe remainingPorts.counter
  have hf := hframe (rescanStacks 22)
  have hm : 64 * F + 100 ≤ (candidate.val + 1) * (64 * F + 100) := by
    simpa only [one_mul] using
      (Nat.mul_le_mul_right (64 * F + 100) (show 1 ≤ candidate.val + 1 by omega))
  calc
    _ ≤ (candidate.val + 1) * AttainedSignatureProgram.Rescan.polynomialBudget W rows h B +
        (64 * F + 100) := by omega
    _ ≤ (candidate.val + 1) * AttainedSignatureProgram.Rescan.polynomialBudget W rows h B +
        (candidate.val + 1) * (64 * F + 100) := Nat.add_le_add_left hm _
    _ = _ := by ring

/-- The fresh final-head branch has the same uniform prefix cap as a losing
candidate: the rescan uses its own bound, while frame storage and cleanup
are charged by their polynomial local execution time. -/
theorem fresh_leaf_run_space (loadHead visit : Cmd 40 896) (a : State 40 896)
    (W : List Bool) (rows : List (List (List Bool))) (h B F address : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hw : CursorWords a h candidate.val)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hleaf : a.regs controllerPorts.leaf = false)
    (hfresh : Bool.not (AttainedSignatures.duplicateScan
      (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate) = true)
    (hpayload : a.stacks (tupleStacks 4) = [])
    (hheads : a.stacks (tupleStacks 6) = [true])
    (haddress : a.stacks (tupleStacks 9) = List.replicate address true)
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hpositive : 1 ≤ F) (hcursor : h + 1 ≤ F)
    (hkey : AttainedSignatureProgram.Rescan.keyBound W h rows.length B ≤ F)
    (hspace : AttainedSignatureProgram.Rescan.spaceBudget W rows h B ≤ F) :
    ∃ n out,
      Eval (body controllerPorts (assembleRoutines loadHead candidateCall visit)) n a
        (descendClearState (probePostState a out W rows h candidate)) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
          prefixSteps (a.withPC (some (compiled
            (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1)) ∧
      n + 1 ≤ (candidate.val + 1) *
        (AttainedSignatureProgram.Rescan.polynomialBudget W rows h B + 64 * F + 100) := by
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false := by
    rw [hw.available]
    simp only [Nat.ne_of_lt candidate.isLt, decide_false]
  obtain ⟨np, hnp, out, hp, hpSpace⟩ := SignatureRescanBridge.probe_run_space
    a W rows h B F hlen hwidth candidate ready hw.decrementScratch hzero hframe
  let b := probePostState a out W rows h candidate
  have hb := probe_endpoint_bound a out W rows h B F candidate ready hw.decrementScratch
    hlen hwidth hframe hpositive hkey
  have hwords := SignatureRescanBridge.probe_preserves_cursor a out W rows h candidate ready hw
  have hflags := SignatureRescanBridge.probe_control_flags a out W rows h candidate hzero
  have hbranch : b.regs controllerPorts.fresh = true := hflags.2.2.2.trans hfresh
  have hf (i : Fin 896) (hk : i ≠ rescanStacks 17) (hl : i ≠ rescanStacks 22) :
      b.stacks i = a.stacks i :=
    SignatureRescanBridge.probe_stack_frame a out W rows h candidate ready hw.decrementScratch i hk hl
  have hbp : b.stacks (tupleStacks 4) = [] := by
    rw [hf _ (by decide) (by decide)]; exact hpayload
  have hbr : b.stacks (tupleStacks 6) = [true] := by
    rw [hf _ (by decide) (by decide)]; exact hheads
  have hbz : b.stacks (tupleStacks 9) = List.replicate address true := by
    rw [hf _ (by decide) (by decide)]; exact haddress
  have hd := descend_leaf_eval loadHead b h candidate address
    (hwords.exact candidate.isLt) hwords.remaining hbp hwords.decrementScratch hbr hbz
  let nd := 22 * h + 31 + clearWordsTime currentHeadPorts (descendLevelState (retainedState b))
  have hclear := clearWordsTime_le_on currentHeadPorts _ F (descend_current_bound b F hbp hb)
  change clearWordsTime currentHeadPorts _ ≤ 8 * (2 * F + 3) at hclear
  have hnd : nd ≤ 38 * F + 55 := by dsimp only [nd]; omega
  have hps : ∀ p q, p ≤ np → Trace (compiled (probeWith candidateCall) 0 0) p
      (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ 2000 * (F + 1) := by
    intro p q hpn hq i
    have hs := hpSpace p q (by omega) hq i
    have hr := hframe remainingPorts.counter
    have hf' := hframe (rescanStacks 22)
    omega
  have hds : ∀ p q, p ≤ nd → Trace (compiled (descendWith loadHead) 0 0) p
      (b.withPC (some (compiled (descendWith loadHead) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ 2000 * (F + 1) := by
    have hh := descend_leaf_stack_bound loadHead b h F hbp hb
    intro p q hpn hq i
    exact (hh p q (by dsimp only [nd] at hpn; omega) hq i).trans (by omega)
  let freshBranch : Cmd 40 896 := .ite controllerPorts.fresh (descendWith loadHead) advanceCandidateCommand
  let availableBranch : Cmd 40 896 := .ite controllerPorts.available freshBranch (ascendWith loadHead)
  have hfe : Eval freshBranch (nd + 1) b (descendClearState b) := .ite_true hbranch hd
  have hfs := StructuredSpace.conditional_true_stack_bound
    (no := advanceCandidateCommand) hbranch hd 0 0 hds
    (compiled freshBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have haveval : Eval availableBranch (nd + 1 + 1) b (descendClearState b) :=
    .ite_true hflags.2.2.1 hfe
  have havspace := StructuredSpace.conditional_true_stack_bound
    (no := ascendWith loadHead) hflags.2.2.1 hfe 0 0 hfs
    (compiled availableBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hseq := hp.seq haveval
  have hsseq := StructuredSpace.sequence_stack_bound hp haveval 0 0 hps havspace
    (compiled (.seq (probeWith candidateCall) availableBranch) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have he : Eval (body controllerPorts (assembleRoutines loadHead candidateCall visit))
      (np + (nd + 1 + 1) + 1) a (descendClearState b) := .ite_false hleaf hseq
  have hwhole := StructuredSpace.conditional_false_stack_bound
    (yes := .seq visit (ascendWith loadHead)) hleaf hseq 0 0 hsseq
    (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  refine ⟨_, out, he, StructuredSpace.compiled_halt_stack_bound he 0 0 hwhole, ?_⟩
  have hr := hframe remainingPorts.counter
  have hf' := hframe (rescanStacks 22)
  have hm : 64 * F + 100 ≤ (candidate.val + 1) * (64 * F + 100) := by
    simpa only [one_mul] using
      (Nat.mul_le_mul_right (64 * F + 100) (show 1 ≤ candidate.val + 1 by omega))
  calc
    _ ≤ (candidate.val + 1) * AttainedSignatureProgram.Rescan.polynomialBudget W rows h B +
        (64 * F + 100) := by omega
    _ ≤ (candidate.val + 1) * AttainedSignatureProgram.Rescan.polynomialBudget W rows h B +
        (candidate.val + 1) * (64 * F + 100) := Nat.add_le_add_left hm _
    _ = _ := by ring

theorem exhausted_root_run_space (loadHead visit : Cmd 40 896)
    (a : State 40 896) (F : ℕ) (hleaf : a.regs controllerPorts.leaf = false)
    (hframes : a.stacks (tupleStacks 0) = [])
    (hs : a.stacks remainingPorts.scratch = [])
    (hz : CounterPrograms.isZero (a.stacks remainingPorts.counter) = true)
    (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∃ n,
      Eval (body controllerPorts (assembleRoutines loadHead candidateCall visit)) n a
        (rootAscendState (testAvailableState a)) ∧
      (rootAscendState (testAvailableState a)).regs controllerPorts.active = false ∧
      (∀ i, ((rootAscendState (testAvailableState a)).stacks i).length ≤ F) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
          prefixSteps (a.withPC (some (compiled
            (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1)) ∧
      n + 1 ≤ 24 * F + 38 := by
  obtain ⟨n, hi, hhalt, htime⟩ := exhausted_root_iteration loadHead visit a F hleaf hframes hs hz hframe
  have htime' : n + 1 ≤ 24 * F + 38 := by
    have hf := hframe remainingPorts.counter
    omega
  refine ⟨n, hi.eval, hhalt, ?_, ?_, htime'⟩
  · intro i
    rw [checkedReturnState_stack, testAvailableState_stacks a hs]
    split_ifs
    · simp
    · exact hframe i
  · have hb := StructuredSpace.local_stack_bound
      (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
      (a := a.withPC (some (compiled
        (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0).entry))
      (steps := 24 * F + 38) (StreamResources.dataBits_le_mul _ hframe)
    intro p q hp hq i
    exact (hb p q (by omega) hq i).trans (by omega)

theorem copyPredecessor_cursor (a : State 40 896) (h candidate : ℕ)
    (hw : CursorWords a h candidate) :
    CursorWords (copyState 651 (tupleStacks 8) a) h candidate := by
  have hf (i : Fin 896) (hi : i ≠ tupleStacks 8) :
      (copyState 651 (tupleStacks 8) a).stacks i = a.stacks i := by
    simp only [copyState, StackRoutines.copyStacks, Function.update_of_ne hi]
  refine ⟨hw.range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf _ (by decide)]; exact hw.value
  · rw [hf _ (by decide)]; exact hw.width
  · intro hc; rw [hf _ (by decide)]; exact hw.exact hc
  · rw [hf _ (by decide)]; exact hw.remaining
  · rw [hf _ (by decide)]; exact hw.incrementScratch
  · rw [hf _ (by decide)]; exact hw.decrementScratch

/-- After the parent matrix reload, reset only the predecessor zero word
and advance the restored cursor once. Earlier candidates are not rescanned. -/
theorem resume_loaded_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (candidate : ℕ) (a : State 40 896)
    (ha : AncestorStorage h key levels base depth.val ancestors a)
    (hw : CursorWords a (h depth.val) candidate) (hc : candidate < 2 ^ h depth.val)
    (hleaf : a.regs controllerPorts.leaf = false)
    (hwidth : a.stacks 651 = List.replicate (h depth.val) false)
    (hp : a.stacks (tupleStacks 4) = []) (hz : a.stacks (tupleStacks 8) = []) :
    ScanStorage h key levels base depth ancestors (candidate + 1)
      (advanceCandidateState (copyState 651 (tupleStacks 8) a)) := by
  let b := copyState 651 (tupleStacks 8) a
  have hf (i : Fin 896) (hi : i ≠ tupleStacks 8) : b.stacks i = a.stacks i := by
    simp only [b, copyState, StackRoutines.copyStacks, Function.update_of_ne hi]
  have hb : AncestorStorage h key levels base depth.val ancestors b := by
    refine ⟨ha.depth_le, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf _ (by decide)]; exact ha.cursors
    · rw [hf _ (by decide)]; exact ha.representatives
    · rw [hf _ (by decide)]; exact ha.heads
    · rw [hf _ (by decide)]; exact ha.address
    · change readRegs a.regs 0 1 none controllerPorts.active = true
      rw [StackRoutines.readRegs_frame _ _ _ _ _ (by decide) (by decide)]
      exact ha.active
  have hl : b.regs controllerPorts.leaf = false := by
    change readRegs a.regs 0 1 none controllerPorts.leaf = false
    rw [StackRoutines.readRegs_frame _ _ _ _ _ (by decide) (by decide)]
    exact hleaf
  have hp' : b.stacks (tupleStacks 4) = [] := by rw [hf _ (by decide)]; exact hp
  have hz' : b.stacks (tupleStacks 8) = List.replicate (h depth.val) false := by
    simp only [b, copyState, StackRoutines.copyStacks, Function.update_self, hwidth, hz, List.append_nil]
  exact advance_scan_storage h key levels base depth ancestors candidate b hb
    (copyPredecessor_cursor a (h depth.val) candidate hw) hc hl hp' hz'

theorem resume_loaded_run_space (a : State 40 896) (h candidate F : ℕ)
    (hw : CursorWords a h candidate) (hc : candidate < 2 ^ h)
    (hwidth : a.stacks 651 = List.replicate h false)
    (hz : a.stacks (tupleStacks 8) = [])
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hcursor : h + 1 ≤ F) :
    ∃ n,
      Eval (.seq resetPredecessorCommand advanceCandidateCommand) n a
        (advanceCandidateState (copyState 651 (tupleStacks 8) a)) ∧
      (∀ i, ((advanceCandidateState (copyState 651 (tupleStacks 8) a)).stacks i).length ≤ F) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (.seq resetPredecessorCommand advanceCandidateCommand) 0 0) prefixSteps
          (a.withPC (some (compiled (.seq resetPredecessorCommand advanceCandidateCommand) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1)) ∧
      n + 1 ≤ 33 * F + 49 := by
  let b := copyState 651 (tupleStacks 8) a
  have hwords := copyPredecessor_cursor a h candidate hw
  have hcopy := copyWord_eval 651 (tupleStacks 8) (tupleStacks 5)
    (by decide) (by decide) (by decide) a hw.decrementScratch
  rw [hwidth, List.length_replicate] at hcopy
  have hadv := advanceCandidate_eval b hwords.incrementScratch hwords.decrementScratch
  have he : Eval (.seq resetPredecessorCommand advanceCandidateCommand)
      (7 * h + 5 + (advanceTime b + 2 * (b.stacks (tupleStacks 3)).length + 3)) a
      (advanceCandidateState b) := hcopy.seq hadv
  have hb : ∀ i, (b.stacks i).length ≤ F := by
    intro i
    by_cases hi : i = tupleStacks 8
    · subst i
      simp only [b, copyState, StackRoutines.copyStacks, Function.update_self,
        hwidth, hz, List.append_nil, List.length_replicate]
      omega
    · simpa only [b, copyState, StackRoutines.copyStacks, Function.update_of_ne hi] using hframe i
  have hpos : 0 < CounterPrograms.value (b.stacks remainingPorts.counter) := by
    rw [hwords.remaining_value]
    omega
  have htime := advanceTime_le b hpos
  rw [hwords.exact hc, hwords.remaining] at htime
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at htime
  have hk := hb (tupleStacks 3)
  have hn : 7 * h + 5 + (advanceTime b + 2 * (b.stacks (tupleStacks 3)).length + 3) + 1 ≤
      33 * F + 49 := by omega
  refine ⟨_, he, advance_endpoint_bound b h candidate F hwords hc hb hcursor, ?_, hn⟩
  have hs := StructuredSpace.local_stack_bound
    (compiled (.seq resetPredecessorCommand advanceCandidateCommand) 0 0)
    (a := a.withPC (some (compiled (.seq resetPredecessorCommand advanceCandidateCommand) 0 0).entry))
    (steps := 33 * F + 49) (StreamResources.dataBits_le_mul _ hframe)
  intro p q hp hq i
  exact (hs p q (by omega) hq i).trans (by omega)

theorem parent_return_current_empty (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (i : Fin 896) (hi : i ∈ currentHeadPorts)
    (h2 : i ≠ tupleStacks 2) (h7 : i ≠ tupleStacks 7) :
    (parentReturnState h key depth ancestors a).stacks i = [] := by
  have hports : i ≠ tupleStacks 0 ∧ i ≠ tupleStacks 1 ∧
      i ≠ tupleStacks 6 ∧ i ≠ tupleStacks 9 := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [parentReturnState, ascendLevelState_outside _ _ hports.2.2.1 hports.2.2.2]
  by_cases h4 : i = tupleStacks 4
  · subst i
    exact (parentWordsState_fields h key depth ancestors a).2.2.2.2
  · rw [parentWordsState_outside _ _ _ _ _ _ hports.1 hports.2.1 h2 h4 h7,
      checkedReturnState_stack, ite_eq_left hi]

theorem parentReturnState_outside_tuple (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) (i : Fin 896)
    (hi : ∀ j : Fin 12, i ≠ tupleStacks j) :
    (parentReturnState h key depth ancestors a).stacks i = a.stacks i := by
  have hc : i ∉ currentHeadPorts := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨hi 2, hi 3, hi 4, hi 5, hi 7, hi 8, hi 10, hi 11⟩
  rw [parentReturnState, ascendLevelState_outside _ _ (hi 6) (hi 9),
    parentWordsState_outside _ _ _ _ _ _ (hi 0) (hi 1) (hi 2) (hi 4) (hi 7),
    checkedReturnState_stack, ite_eq_right hc]

/-- Restoring a suspended parent again fits the same global frame and word
cap before its matrix is reloaded. No transient cost is accumulated. -/
theorem parent_return_endpoint_bound (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base depth hmax F : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (ha : AncestorStorage h key levels base (depth + 1) ancestors a)
    (hh : ∀ d < levels, h d ≤ hmax)
    (hcap : 6 * levels * (hmax + 1) + (base + levels) + (hmax + 1) ≤ F)
    (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∀ i, ((parentReturnState h key depth ancestors a).stacks i).length ≤ F := by
  have hb := parent_return_ancestor_storage h key levels base depth ancestors a ha
  have hw := parent_return_cursor h key depth ancestors a
  have hf := hb.frame_bound h key hmax hh
  have hd : depth < levels := by have := ha.depth_le; omega
  have hwidth := hh depth hd
  have hz (i : Fin 896) (hi : i ∈ currentHeadPorts)
      (h2 : i ≠ tupleStacks 2) (h7 : i ≠ tupleStacks 7) :
      (parentReturnState h key depth ancestors a).stacks i = [] :=
    parent_return_current_empty h key depth ancestors a i hi h2 h7
  intro i
  by_cases hi : ∃ j : Fin 12, i = tupleStacks j
  · obtain ⟨j, rfl⟩ := hi
    fin_cases j
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 0)).length ≤ F
      omega
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 1)).length ≤ F
      omega
    · change ((parentReturnState h key depth ancestors a).stacks candidatePorts.counter).length ≤ F
      have := hw.width
      omega
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 3)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 4)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 5)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 6)).length ≤ F
      rw [hb.heads, List.length_replicate]
      omega
    · change ((parentReturnState h key depth ancestors a).stacks remainingPorts.counter).length ≤ F
      rw [hw.remaining, ExecCNFTupleEnumeration.fixedBits_length]
      omega
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 8)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 9)).length ≤ F
      rw [hb.address, List.length_replicate]
      omega
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 10)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 11)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
  · rw [parentReturnState_outside_tuple h key depth ancestors a i (fun j hj => hi ⟨j, hj⟩)]
    exact hframe i

/-- A nonroot return composes the actual bounded frame restoration, actual
matrix reload evaluation, and one cursor advance. Its storage estimate uses
only this polynomial reload time, never the preceding traversal length. -/
theorem ascend_loaded_run_space (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (loadHead : Cmd 40 896)
    (depth F loadSteps : ℕ) (ancestors : Prefix (Representatives key) (depth + 1))
    (a loaded : State 40 896)
    (hframes : a.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) ancestors)
    (hreps : a.stacks (tupleStacks 1) = representativeFrames h key (depth + 1) ancestors)
    (hload : Eval loadHead loadSteps (parentReturnState h key depth ancestors a) loaded)
    (hwords : CursorWords loaded (h depth) (ancestors (Fin.last depth)).val.val)
    (hwidth : loaded.stacks 651 = List.replicate (h depth) false)
    (hz : loaded.stacks (tupleStacks 8) = [])
    (hframe : ∀ i, (a.stacks i).length ≤ F)
    (hloaded : ∀ i, (loaded.stacks i).length ≤ F) (hcursor : h depth + 1 ≤ F) :
    ∃ n,
      Eval (ascendWith loadHead) n a (advanceCandidateState (copyState 651 (tupleStacks 8) loaded)) ∧
      (∀ i, ((advanceCandidateState (copyState 651 (tupleStacks 8) loaded)).stacks i).length ≤ F) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (ascendWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1) + loadSteps) ∧
      n + 1 ≤ loadSteps + 69 * F + 100 := by
  obtain ⟨nt, ht, hend, _, hnt⟩ := resume_loaded_run_space loaded (h depth)
    (ancestors (Fin.last depth)).val.val F hwords (ancestors (Fin.last depth)).val.isLt
    hwidth hz hloaded hcursor
  have hp := parent_return_prefix_eval h key depth ancestors a hframes hreps
  have hresume : Eval (resumeParentWith loadHead) (20 * h depth + 25 + loadSteps + nt)
      (rootAscendState a) (advanceCandidateState (copyState 651 (tupleStacks 8) loaded)) := by
    generalize hcost : 20 * h depth + 25 = frameSteps at hp
    cases hp with
    | seq hdrop hrest =>
      cases hrest with
      | seq hrestore hascend =>
        have he := hdrop.seq (hrestore.seq (hascend.seq (hload.seq ht)))
        change Eval (resumeParentWith loadHead) _ (rootAscendState a) _ at he
        convert he using 1
        omega
  have hb : Eval (.ite controllerPorts.active (resumeParentWith loadHead) (.base .skip))
      (20 * h depth + 25 + loadSteps + nt + 1) (rootAscendState a)
      (advanceCandidateState (copyState 651 (tupleStacks 8) loaded)) :=
    .ite_true (checkedReturnState_active h key depth ancestors a hframes) hresume
  have hall := (clearWords_eval currentHeadPorts a).seq
    ((testParent_eval (clearWordsState currentHeadPorts a)).seq hb)
  change Eval (ascendWith loadHead) _ a _ at hall
  have hc := clearWordsTime_le_on currentHeadPorts a F (fun i _ => hframe i)
  change clearWordsTime currentHeadPorts a ≤ 8 * (2 * F + 3) at hc
  have hn : clearWordsTime currentHeadPorts a +
      (1 + (20 * h depth + 25 + loadSteps + nt + 1)) + 1 ≤ loadSteps + 69 * F + 100 := by omega
  refine ⟨_, hall, hend, ?_, hn⟩
  have hs := StructuredSpace.local_stack_bound (compiled (ascendWith loadHead) 0 0)
    (a := a.withPC (some (compiled (ascendWith loadHead) 0 0).entry))
    (steps := loadSteps + 69 * F + 100) (StreamResources.dataBits_le_mul _ hframe)
  intro p q hp hq i
  exact (hs p q (by omega) hq i).trans (by omega)

theorem reset_candidate_ready (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h : ℕ)
    (hW : a.stacks 141 = W)
    (hrows : a.stacks 847 = Subexp.MatrixProgramSupport.words (rows.map Subexp.MatrixProgramSupport.words))
    (hw : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hs : a.stacks (tupleStacks 3) = [])
    (hp : a.stacks (tupleStacks 4) = []) (hpred : a.stacks (tupleStacks 8) = [])
    (hscratch : ∀ i : Fin 24, i ≠ 0 → i ≠ 15 → i ≠ 16 → i ≠ 17 → i ≠ 18 → i ≠ 22 →
      a.stacks (rescanStacks i) = []) :
    CandidateReady (resetGeneratorState a) W rows h ⟨0, Nat.pow_pos (by decide)⟩ := by
  have outside (i : Fin 24) (h16 : i ≠ 16) (h18 : i ≠ 18) :
      (resetGeneratorState a).stacks (rescanStacks i) = a.stacks (rescanStacks i) := by
    apply resetGeneratorState_outside <;> fin_cases i <;> first | contradiction | decide
  have hzero : List.replicate h false = ExecCNFTupleEnumeration.fixedBits h 0 :=
    (resetState_words a h hw hc hp).1.symm.trans (resetState_assignment a h hw hc hp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [outside 0 (by decide) (by decide)]
    exact hW
  · rw [outside 15 (by decide) (by decide)]
    exact hrows
  · change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) (tupleStacks 2) = _
    rw [Function.update_of_ne (by decide)]
    exact resetState_assignment a h hw hc hp
  · rw [outside 17 (by decide) (by decide)]
    exact hs
  · rw [rescanStacks_predecessor, resetGeneratorState_predecessor a h hw hpred]
    exact hzero
  · intro i h0 h15 h16 h17 h18 h22
    rw [outside i h16 h18]
    exact hscratch i h0 h15 h16 h17 h18 h22


theorem reset_endpoint_bound (a : State 40 896) (h F : ℕ)
    (hh : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = [])
    (ht : a.stacks (tupleStacks 5) = []) (hz : a.stacks (tupleStacks 8) = [])
    (hi : a.stacks (tupleStacks 10) = [])
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hwidth : h + 1 ≤ F) :
    ∀ i, ((resetGeneratorState a).stacks i).length ≤ F := by
  have hw := resetGeneratorState_cursor a h hh hc hp ht hi
  intro i
  by_cases h2 : i = tupleStacks 2
  · subst i
    exact hw.width.trans hwidth
  · by_cases h4 : i = tupleStacks 4
    · subst i
      change (Function.update (resetState a).stacks (tupleStacks 8)
        ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) (tupleStacks 4)).length ≤ F
      rw [Function.update_of_ne (by decide), (resetState_words a h hh hc hp).2.2]
      simp
    · by_cases h7 : i = tupleStacks 7
      · subst i
        rw [show (resetGeneratorState a).stacks (tupleStacks 7) = _ from hw.remaining,
          ExecCNFTupleEnumeration.fixedBits_length]
        exact hwidth
      · by_cases h8 : i = tupleStacks 8
        · subst i
          rw [resetGeneratorState_predecessor a h hh hz, List.length_replicate]
          omega
        · rw [resetGeneratorState_outside a i h2 h4 h7 h8]
          exact hframe i

/-- Positive-depth setup reaches the first head through its actual loader
run and the fixed bounded-memory initializer. -/
theorem setup_loaded_run_space (loadHead : Cmd 40 896) (a loaded : State 40 896)
    (levels base h F loadSteps : ℕ) (hlevels : 0 < levels)
    (hheads : a.stacks 130 = List.replicate levels true)
    (hbase : a.stacks 649 = List.replicate base true)
    (hload : Eval loadHead loadSteps (initialControlState a) loaded)
    (hh : loaded.stacks 651 = List.replicate h false)
    (hc : loaded.stacks (tupleStacks 2) = []) (hp : loaded.stacks (tupleStacks 4) = [])
    (ht : loaded.stacks (tupleStacks 5) = []) (hr : loaded.stacks (tupleStacks 7) = [])
    (hz : loaded.stacks (tupleStacks 8) = []) (hi : loaded.stacks (tupleStacks 10) = [])
    (hframe : ∀ i, (a.stacks i).length ≤ F)
    (hloaded : ∀ i, (loaded.stacks i).length ≤ F) (hcursor : h + 1 ≤ F) :
    ∃ n,
      Eval (setupWith loadHead) n a (resetGeneratorState loaded) ∧
      (∀ i, ((resetGeneratorState loaded).stacks i).length ≤ F) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (setupWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1) + loadSteps) ∧
      n + 1 ≤ loadSteps + 63 * F + 73 := by
  have hinit := initializeLevels_eval (initialClearState a) (initialClearState_tuple a 5)
  rw [initialClearState_source130, initialClearState_source649, hheads, hbase,
    List.length_replicate, List.length_replicate] at hinit
  have hl : (initialControlState a).regs controllerPorts.leaf = false := by
    rw [(initialControlState_flags a levels hheads).2]
    simp only [Nat.ne_of_gt hlevels, decide_false]
  have hreset := resetGenerator_eval loaded h hh hr ht hp
  have hb : Eval (.ite controllerPorts.leaf (.base .skip) (.seq loadHead resetGeneratorCommand))
      (loadSteps + (25 * h + 22) + 1) (initialControlState a) (resetGeneratorState loaded) :=
    .ite_false hl (hload.seq hreset)
  have he := (clearWords_eval (List.ofFn tupleStacks) a).seq (hinit.seq hb)
  change Eval (setupWith loadHead) _ a (resetGeneratorState loaded) at he
  have hclear := clearWordsTime_le_on (List.ofFn tupleStacks) a F (fun i _ => hframe i)
  rw [List.length_ofFn] at hclear
  have hlevelsF := hframe 130
  have hbaseF := hframe 649
  rw [hheads, List.length_replicate] at hlevelsF
  rw [hbase, List.length_replicate] at hbaseF
  have hn : clearWordsTime (List.ofFn tupleStacks) a +
      (7 * levels + 7 * base + 13 + (loadSteps + (25 * h + 22) + 1)) + 1 ≤
      loadSteps + 63 * F + 73 := by omega
  refine ⟨_, he, reset_endpoint_bound loaded h F hh hc hp ht hz hi hloaded hcursor, ?_, hn⟩
  have hs := StructuredSpace.local_stack_bound (compiled (setupWith loadHead) 0 0)
    (a := a.withPC (some (compiled (setupWith loadHead) 0 0).entry))
    (steps := loadSteps + 63 * F + 73) (StreamResources.dataBits_le_mul _ hframe)
  intro p q hp hq i
  exact (hs p q (by omega) hq i).trans (by omega)

/-- A losing candidate changes only its two cursor words and the freshness
latch. In particular all accumulators, retained inputs, and caches survive. -/
theorem duplicate_stack_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hw : CursorWords a h candidate.val) (i : Fin 896)
    (hc : i ≠ candidatePorts.counter) (hr : i ≠ remainingPorts.counter)
    (hf : i ≠ rescanStacks 22) :
    (advanceCandidateState (probePostState a out W rows h candidate)).stacks i = a.stacks i := by
  let b := probePostState a out W rows h candidate
  have hb := SignatureRescanBridge.probe_preserves_cursor a out W rows h candidate ready hw
  have hn := hb.advance candidate.isLt
  by_cases hk : i = tupleStacks 3
  · subst i
    change Function.update (advanceState b).stacks (tupleStacks 3) [] (tupleStacks 3) = _
    rw [Function.update_self]
    exact ready.saved.symm
  · by_cases hs : i = remainingPorts.scratch
    · subst i
      rw [hn.decrementScratch, hw.decrementScratch]
    · rw [advanceCandidateState_outside b hb.incrementScratch i hk hc hr hs]
      exact SignatureRescanBridge.probe_stack_frame a out W rows h candidate ready
        hw.decrementScratch i hk hf

theorem duplicate_register_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (j : Fin 40) (hj : 16 ≤ j.val)
    (ha : j ≠ controllerPorts.available) (hf : j ≠ controllerPorts.fresh) :
    (advanceCandidateState (probePostState a out W rows h candidate)).regs j = a.regs j := by
  rw [advanceCandidateState_register_frame _ j (by omega) ha]
  exact SignatureRescanBridge.probe_register_frame a out W rows h candidate j hj ha hf

theorem fresh_descent_stack_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) (i : Fin 896)
    (hi : ∀ j : Fin 12, i ≠ tupleStacks j) (hf : i ≠ rescanStacks 22) :
    (descendClearState (probePostState a out W rows h candidate)).stacks i = a.stacks i := by
  rw [descendClearState_outside_tuple _ i hi]
  exact SignatureRescanBridge.probe_stack_frame a out W rows h candidate ready hs i (hi 3) hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
