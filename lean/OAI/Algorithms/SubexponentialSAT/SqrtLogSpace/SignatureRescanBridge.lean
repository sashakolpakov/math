import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative

/-!
# Physical effects of one full-signature probe

The input readiness facts describe actual words. The native predicate itself
supplies the run; its returned freshness is the first-occurrence predicate for
the complete integer signature.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open AttainedSignatureProgram.Rescan

theorem probe_stacks (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) :
    (probePostState a out W rows h candidate).stacks =
      Function.update (Function.update a.stacks (rescanStacks 17)
        (naturalKey W rows h candidate)) (rescanStacks 22)
        [!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)] := by
  classical
  let pre := probePreState a
  let initial := workState (pre.regs ∘ rescanRegisters) W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) []
    (ExecCNFTupleEnumeration.fixedBits h 0) [] false [] []
  let key := naturalKey W rows h candidate
  let fresh := !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)
  have hz : ExecCNFTupleEnumeration.fixedBits h 0 = List.replicate h false :=
    ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
      (by simp [ExecCNFTupleEnumeration.fixedBits_value h 0 (Nat.pow_pos (by decide))])
  have hlocal : (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
      key (List.replicate h false) [] fresh [] []).stacks =
      Function.update (Function.update initial.stacks 17 key) 22 [fresh] := by
    dsimp [initial]
    rw [hz]
    funext i
    fin_cases i <;> simp [workState]
  have hemb : Function.extend rescanStacks initial.stacks pre.stacks = pre.stacks := by
    change (embedState rescanRegisters rescanStacks pre initial).stacks = pre.stacks
    have hi : projectState rescanRegisters rescanStacks pre = initial := ready.probe_projection hs
    rw [← hi, embedState_project _ _ _ rescanRegisters.injective rescanStacks.injective]
  change Function.extend rescanStacks _ pre.stacks = _
  rw [hlocal, ProgramLinking.extend_update rescanStacks.injective,
    ProgramLinking.extend_update rescanStacks.injective, hemb]
  change Function.update (Function.update (probePreState a).stacks (rescanStacks 17) key)
    (rescanStacks 22) [fresh] = _
  rw [probePreState_stacks a hs]
  funext j
  by_cases h17 : j = rescanStacks 17
  · subst j
    simp only [Function.update_self, Function.update_of_ne
      (by decide : rescanStacks 17 ≠ rescanStacks 22)]
    rfl
  · by_cases h22 : j = rescanStacks 22
    · subst j; simp only [Function.update_self]; rfl
    · simp only [Function.update_of_ne h17, Function.update_of_ne h22]

theorem probe_stack_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) (j : Fin 896)
    (hk : j ≠ rescanStacks 17) (hf : j ≠ rescanStacks 22) :
    (probePostState a out W rows h candidate).stacks j = a.stacks j := by
  rw [probe_stacks a out W rows h candidate ready hs]
  rw [Function.update_of_ne hf, Function.update_of_ne hk]

theorem probe_preserves_cursor (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (cursor : CursorWords a h candidate) :
    CursorWords (probePostState a out W rows h candidate) h candidate := by
  have hc := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    candidatePorts.counter (by decide) (by decide)
  have hr := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    remainingPorts.counter (by decide) (by decide)
  have hcs := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    candidatePorts.scratch (by decide) (by decide)
  have hrs := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    remainingPorts.scratch (by decide) (by decide)
  exact ⟨cursor.range, hc ▸ cursor.value, hc ▸ cursor.width,
    fun hi => hc.trans (cursor.exact hi), hr.trans cursor.remaining,
    hcs.trans cursor.incrementScratch, hrs.trans cursor.decrementScratch⟩

theorem test_available_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (ha : j ≠ controllerPorts.available) :
    (testAvailableState a).regs j = a.regs j := by
  have h2 : j ≠ remainingPorts.register 2 := by
    intro he
    have hv := congrArg Fin.val he
    change j.val = 2 at hv
    omega
  simp only [testAvailableState, CounterForPrograms.testResult,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    Function.update_of_ne ha, Function.update_of_ne h2]
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hil := i.isLt
  change i.val = j.val at hv
  omega

theorem probe_register_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (j : Fin 40) (hj : 16 ≤ j.val)
    (ha : j ≠ controllerPorts.available) (hf : j ≠ controllerPorts.fresh) :
    (probePostState a out W rows h candidate).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro he; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro he; subst j; norm_num at hj
  change readRegs (candidateOutput (probePreState a) out W rows h candidate).regs
    controllerPorts.fresh 0 _ j = _
  rw [StackRoutines.readRegs_frame _ _ _ _ _ hf h0,
    candidateOutput_flag _ _ _ _ _ _ _ hj]
  rw [probePreState, initializeFreshState_controller _ _ h0 h1]
  exact test_available_register_frame a j (by omega) ha

theorem probe_control_flags (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h))
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false) :
    (probePostState a out W rows h candidate).regs controllerPorts.active =
        a.regs controllerPorts.active ∧
      (probePostState a out W rows h candidate).regs controllerPorts.leaf =
        a.regs controllerPorts.leaf ∧
      (probePostState a out W rows h candidate).regs controllerPorts.available = true ∧
      (probePostState a out W rows h candidate).regs controllerPorts.fresh =
        !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate) :=
  ⟨probe_register_frame a out W rows h candidate _ (by decide) (by decide) (by decide),
    probe_register_frame a out W rows h candidate _ (by decide) (by decide) (by decide),
    probePostState_flags a out W rows h candidate hnonzero⟩

theorem probe_integer_fresh {h d : ℕ} (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) + A j i) (candidate : Fin (2 ^ h))
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false) :
    (probePostState a out W (List.ofFn (fun j => List.ofFn (c j))) h candidate).regs
        controllerPorts.fresh = true ↔
      ∀ j, j < candidate → AttainedSignatures.integerKey A j ≠
        AttainedSignatures.integerKey A candidate := by
  rw [(probePostState_flags a out W _ h candidate hnonzero).2]
  exact SignatureTupleTraversal.actual_fresh_iff_model _ _
    (naturalKey_eq_iff W c A hc) candidate

theorem probe_integer_duplicate {h d : ℕ} (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) + A j i) (candidate : Fin (2 ^ h))
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false) :
    (probePostState a out W (List.ofFn (fun j => List.ofFn (c j))) h candidate).regs
        controllerPorts.fresh = false ↔
      ¬ ∀ j, j < candidate → AttainedSignatures.integerKey A j ≠
        AttainedSignatures.integerKey A candidate := by
  rw [(probePostState_flags a out W _ h candidate hnonzero).2]
  exact SignatureTupleTraversal.actual_duplicate_iff_model _ _
    (naturalKey_eq_iff W c A hc) candidate

private theorem sequence_prefix {first second : Cmd 40 896} {n m bound : ℕ}
    {a b c : State 40 896} (hf : Eval first n a b) (hs : Eval second m b c)
    (hfirst : ∀ p q, p ≤ n → Trace (compiled first 0 0) p
      (a.withPC (some (compiled first 0 0).entry)) q → ∀ i, (q.stacks i).length ≤ bound)
    (hsecond : ∀ p q, p ≤ m → Trace (compiled second 0 0) p
      (b.withPC (some (compiled second 0 0).entry)) q → ∀ i, (q.stacks i).length ≤ bound) :
    ∀ p q, p ≤ n + m → Trace (compiled (.seq first second) 0 0) p
      (a.withPC (some (compiled (.seq first second) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ bound :=
  StructuredSpace.sequence_stack_bound hf hs 0 0 hfirst hsecond
    (compiled (.seq first second) 0 0) (siteAddress _) (exitAddress _)
    (compiled_site _ 0 0)

/-- Uniform storage for the full probe, including its availability test,
latch initialization, compiled candidate call, readback and final halt.
The numeric candidate appears only in time, never in the storage bound. -/
theorem probe_run_space (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h B frameBound : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = [])
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false)
    (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
    ∃ n ≤ (candidate.val + 1) * polynomialBudget W rows h B +
        8 * (a.stacks remainingPorts.counter).length +
        2 * (a.stacks (rescanStacks 22)).length + 16, ∃ out,
      Eval (probeWith candidateCall) n a (probePostState a out W rows h candidate) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (probeWith candidateCall) 0 0) prefixSteps
          (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * (spaceBudget W rows h B + frameBound + 1) +
            8 * (a.stacks remainingPorts.counter).length +
            2 * (a.stacks (rescanStacks 22)).length + 20 := by
  let t := testAvailableState a
  let pre := probePreState a
  let readback : Cmd 40 896 := .base (.atom (.peek (rescanStacks 22) controllerPorts.fresh 0))
  let totalBound := 896 * (spaceBudget W rows h B + frameBound + 1) +
    8 * (a.stacks remainingPorts.counter).length +
    2 * (a.stacks (rescanStacks 22)).length + 20
  have htwords : t.stacks = a.stacks := testAvailableState_stacks a hs
  have hpre : ∀ i, (pre.stacks i).length ≤ frameBound + 1 := by
    intro i
    change ((probePreState a).stacks i).length ≤ _
    rw [probePreState_stacks a hs]
    by_cases hi : i = rescanStacks 22
    · subst i; simp
    · rw [Function.update_of_ne hi]
      exact (hframe i).trans (Nat.le_succ _)
  have hi : candidateInput pre (pre.regs ∘ rescanRegisters) W rows h candidate false = pre := by
    unfold candidateInput
    rw [← ready.probe_projection hs]
    exact embedState_project _ _ _ rescanRegisters.injective rescanStacks.injective
  obtain ⟨nc, hnc, out, hce, hct, hcp⟩ := SignatureTupleNative.candidate_run pre
    (pre.regs ∘ rescanRegisters) W rows h B (frameBound + 1) hlen hwidth hpre candidate false
  rw [hi] at hce hct hcp
  let finish := candidateOutput pre out W rows h candidate
  have hfinish : ∀ i, (finish.stacks i).length ≤ spaceBudget W rows h B + frameBound + 1 := by
    intro i
    have hb := hcp nc (finish.withPC none) le_rfl hct i
    exact hb.trans (by omega)
  have htest := testAvailable_eval a hs
  have hinit := initializeFresh_eval t
  rw [htwords] at hinit
  have hread : Eval readback 1 finish (probePostState a out W rows h candidate) :=
    .base (.atom (.peek (rescanStacks 22) controllerPorts.fresh 0) finish)
  have hav : t.regs controllerPorts.available = true := by
    rw [testAvailableState_flag, hnonzero]
    rfl
  have hrest := hinit.seq (hce.seq hread)
  have hall := htest.seq (Eval.ite_true (no := .base .skip) hav hrest)
  change Eval (probeWith candidateCall) _ a (probePostState a out W rows h candidate) at hall
  have htestSpace : ∀ p q, p ≤ 8 * (a.stacks remainingPorts.counter).length + 8 →
      Trace (compiled testAvailableCommand 0 0) p
        (a.withPC (some (compiled testAvailableCommand 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ totalBound := by
    have hb := StructuredSpace.local_stack_bound (compiled testAvailableCommand 0 0)
      (a := a.withPC (some (compiled testAvailableCommand 0 0).entry))
      (steps := 8 * (a.stacks remainingPorts.counter).length + 8)
      (StreamResources.dataBits_le_mul _ hframe)
    intro p q hp hq i
    exact (hb p q hp hq i).trans (by dsimp [totalBound]; omega)
  have hinitSpace : ∀ p q, p ≤ 2 * (a.stacks (rescanStacks 22)).length + 5 →
      Trace (compiled initializeFreshCommand 0 0) p
        (t.withPC (some (compiled initializeFreshCommand 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ totalBound := by
    have htframe : ∀ i, (t.stacks i).length ≤ frameBound := by
      rw [htwords]
      exact hframe
    have hb := StructuredSpace.local_stack_bound (compiled initializeFreshCommand 0 0)
      (a := t.withPC (some (compiled initializeFreshCommand 0 0).entry))
      (steps := 2 * (a.stacks (rescanStacks 22)).length + 5)
      (StreamResources.dataBits_le_mul _ htframe)
    intro p q hp hq i
    exact (hb p q hp hq i).trans (by dsimp [totalBound]; omega)
  have hcandidateSpace : ∀ p q, p ≤ nc → Trace (compiled candidateCall 0 0) p
      (pre.withPC (some (compiled candidateCall 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ totalBound := by
    apply StructuredSpace.call_stack_bound candidateMachine (compiled candidateCall 0 0)
      (siteAddress candidateCall) (exitAddress candidateCall)
      (fun pc => compiled_site candidateCall 0 0 pc) hct
    intro p q hp hq i
    exact (hcp p q hp hq i).trans (by dsimp [totalBound]; omega)
  have hreadSpace : ∀ p q, p ≤ 1 → Trace (compiled readback 0 0) p
      (finish.withPC (some (compiled readback 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ totalBound := by
    have hb := StructuredSpace.local_stack_bound (compiled readback 0 0)
      (a := finish.withPC (some (compiled readback 0 0).entry)) (steps := 1)
      (StreamResources.dataBits_le_mul _ hfinish)
    intro p q hp hq i
    exact (hb p q hp hq i).trans (by dsimp [totalBound]; omega)
  have htailSpace := sequence_prefix hce hread hcandidateSpace hreadSpace
  have hrestSpace := sequence_prefix hinit (hce.seq hread) hinitSpace htailSpace
  have hbranchSpace := StructuredSpace.conditional_true_stack_bound
    (no := .base .skip) hav hrest 0 0 hrestSpace
    (compiled (.ite controllerPorts.available _ (.base .skip)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hwholeSpace := sequence_prefix htest (Eval.ite_true (no := .base .skip) hav hrest) htestSpace hbranchSpace
  refine ⟨_, ?_, out, hall, ?_⟩
  · omega
  · exact StructuredSpace.compiled_halt_stack_bound hall 0 0 hwholeSpace

theorem exhausted_probe_space (a : State 40 896) (frameBound : ℕ)
    (hs : a.stacks remainingPorts.scratch = [])
    (hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = true)
    (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
    Trace (compiled (probeWith candidateCall) 0 0)
        (8 * (a.stacks remainingPorts.counter).length + 10)
        (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry))
        ((testAvailableState a).withPC none) ∧
      ∀ prefixSteps intermediate,
        prefixSteps ≤ 8 * (a.stacks remainingPorts.counter).length + 10 →
        Trace (compiled (probeWith candidateCall) 0 0) prefixSteps
          (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * frameBound + 8 * (a.stacks remainingPorts.counter).length + 10 := by
  constructor
  · exact compiled_halt_trace (probe_exhausted_eval a hs hzero) 0 0
  · have hb := StructuredSpace.local_stack_bound (compiled (probeWith candidateCall) 0 0)
      (a := a.withPC (some (compiled (probeWith candidateCall) 0 0).entry))
      (steps := 8 * (a.stacks remainingPorts.counter).length + 10)
      (StreamResources.dataBits_le_mul _ hframe)
    simpa only [Nat.add_assoc] using hb

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge
