import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CounterLoops
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

/-! Sharp storage bounds for binary head-assignment controllers. Only the
counter's retained word length enters the local controller budget; every other
caller stack retains the same envelope throughout arbitrarily many visits. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace

open BitProgram StructuredCalls CounterPrograms CounterForPrograms

private theorem local_call_space {R S labels steps bound : ℕ} (p : Ports R S)
    (program : Program 3 2 labels) (a : State R S) (b : State 3 2)
    (hs : a.stacks p.scratch = [])
    (hrun : Trace program steps
      ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
        (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some program.entry))
      (b.withPC none))
    (hlocal : ∀ q z, q ≤ steps → Trace program q
      ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
        (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some program.entry)) z →
      ∀ i, (z.stacks i).length ≤ bound)
    (hframe : ∀ i, (a.stacks i).length ≤ bound) :
    let command := Cmd.call (ProgramLinking.liftProgram program p.register (stackPorts p))
    ∀ q z, q ≤ steps → Trace (compiled command p.counter p.counter) q
      (a.withPC (some (compiled command p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  dsimp only
  have hstart : install p a (a.regs (p.register 0)) (a.regs (p.register 1))
      (a.regs (p.register 2)) (a.stacks p.counter) [] = a := by
    rw [← hs]
    exact install_self p a
  have he := eval_call_lifted program p.register (stackPorts p) a
    p.register.injective (stackPorts p).injective hrun
  change Eval (.call (ProgramLinking.liftProgram program p.register (stackPorts p))) steps
    (install p a (a.regs (p.register 0)) (a.regs (p.register 1))
      (a.regs (p.register 2)) (a.stacks p.counter) [])
    (embedState p.register (stackPorts p) a b) at he
  rw [hstart] at he
  have hglobal := StructuredSpace.liftProgram_stack_bound program p.register (stackPorts p)
    (a.withPC none) p.register.injective (stackPorts p).injective hrun hlocal hframe
  have hinit : ProgramLinking.embedCfg p.register (stackPorts p) id none (a.withPC none)
      ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
        (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some program.entry)) =
      a.withPC (some (ProgramLinking.liftProgram program p.register (stackPorts p)).entry) := by
    change (install p a _ _ _ _ []).withPC _ = _
    rw [hstart]
    rfl
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases he with
  | call prog ht =>
      exact StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site (.call (ProgramLinking.liftProgram program p.register (stackPorts p)))
          p.counter p.counter) ht hglobal

/-- Increment and decrement use only a two-stack local footprint. -/
theorem ripple_space {R S bound : ℕ} (p : Ports R S) (carry : Bool) (a : State R S)
    (hs : a.stacks p.scratch = []) (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hbudget : 9 * (a.stacks p.counter).length + 8 ≤ bound) :
    let command := Cmd.call (ProgramLinking.liftProgram (rippleProgram carry)
      p.register (stackPorts p))
    ∀ q z, q ≤ rippleCost carry (a.stacks p.counter) + 1 →
      Trace (compiled command p.counter p.counter) q
        (a.withPC (some (compiled command p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  apply local_call_space p (rippleProgram carry) a _ hs
    (ripple_local_trace carry _ _ _ (a.stacks p.counter)) _ hframe
  intro q z hq hz i
  exact (Counters.ripple_prefix_stack_bound carry _ _ _ (a.stacks p.counter) hq hz i).trans
    hbudget

/-- The restoring zero test has the same bound independently of its counter value. -/
theorem zero_space {R S bound : ℕ} (p : Ports R S) (a : State R S)
    (hs : a.stacks p.scratch = []) (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hbudget : 9 * (a.stacks p.counter).length + 8 ≤ bound) :
    ∀ q z, q ≤ 8 * (a.stacks p.counter).length + 6 →
      Trace (compiled (zeroCmd p) p.counter p.counter) q
        (a.withPC (some (compiled (zeroCmd p) p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  apply local_call_space p zeroProgram a _ hs
    (zero_local_trace _ _ _ (a.stacks p.counter)) _ hframe
  intro q z hq hz i
  have hsize : dataBits ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
      (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some zeroProgram.entry)) ≤
      (a.stacks p.counter).length := by
    simp [dataBits, stackBits, localData, counterStacks, Fin.sum_univ_two]
  have hg := StructuredSpace.local_stack_bound zeroProgram hsize q z hq hz i
  omega

/-- Adding the one Boolean negation changes no stack. -/
theorem test_space {R S bound : ℕ} (p : Ports R S) (a : State R S)
    (hs : a.stacks p.scratch = []) (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hbudget : 9 * (a.stacks p.counter).length + 8 ≤ bound) :
    ∀ q z, q ≤ 8 * (a.stacks p.counter).length + 7 →
      Trace (compiled (testCmd p) p.counter p.counter) q
        (a.withPC (some (compiled (testCmd p) p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  have he := zero_eval p a hs
  have hfirst := zero_space p a hs hframe hbudget
  have hmiddle := hfirst _ _ le_rfl (compiled_trace he p.counter p.counter)
  have hnot := Eval.base (StructuredProgram.Eval.atom
    (.bnot (p.register 2) (p.register 2)) (zeroResult p a))
  have hsecond : ∀ q z, q ≤ 1 →
      Trace (compiled (.base (.atom (.bnot (p.register 2) (p.register 2))))
        p.counter p.counter) q ((zeroResult p a).withPC (some
          (compiled (.base (.atom (.bnot (p.register 2) (p.register 2))))
            p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
    intro q z hq hz
    have hcases : q = 0 ∨ q = 1 := by omega
    rcases hcases with rfl | rfl
    · cases hz
      exact hmiddle
    · rw [trace_same_length_unique hz (compiled_trace hnot p.counter p.counter)]
      exact hmiddle
  have whole := StructuredSpace.sequence_stack_bound he hnot p.counter p.counter hfirst
    hsecond (compiled (testCmd p) p.counter p.counter) (siteAddress (testCmd p))
    (exitAddress (testCmd p)) (compiled_site (testCmd p) p.counter p.counter)
  simpa only [StructuredCalls.compiled, Nat.add_assoc] using whole

/-- The complete countdown transition preserves one caller envelope. -/
theorem advance_space {R S bound : ℕ} (p : Ports R S) (a : State R S)
    (hs : a.stacks p.scratch = []) (hp : 0 < value (a.stacks p.counter))
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hbudget : 9 * (a.stacks p.counter).length + 8 ≤ bound) :
    ∀ q z, q ≤ advanceCost p a →
      Trace (compiled (advanceCmd p) p.counter p.counter) q
        (a.withPC (some (compiled (advanceCmd p) p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  have he := decrement_eval p a hs
  have hfirst := ripple_space p false a hs hframe hbudget
  have hmiddle := hfirst _ _ le_rfl (compiled_trace he p.counter p.counter)
  have hbudget' : 9 * ((decrementResult p a).stacks p.counter).length + 8 ≤ bound := by
    rw [decrementResult_counter, decrement_length hp]
    exact hbudget
  have whole := StructuredSpace.sequence_stack_bound he
    (test_eval p (decrementResult p a) (decrementResult_scratch p a))
    p.counter p.counter hfirst
    (test_space p (decrementResult p a) (decrementResult_scratch p a) hmiddle hbudget')
    (compiled (advanceCmd p) p.counter p.counter) (siteAddress (advanceCmd p))
    (exitAddress (advanceCmd p)) (compiled_site (advanceCmd p) p.counter p.counter)
  simpa only [StructuredCalls.compiled, advanceCost, decrementResult_counter] using whole


/-- Every binary-counted visit keeps one fixed bound, including caller frames.
Only the counter word width enters the controller-local side condition. -/
theorem visits_space_next {R S bound width : ℕ} (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hwidth : ∀ i d, I i d → (d.stacks p.counter).length ≤ width)
    (hbudget : 9 * width + 8 ≤ bound)
    (hnext : ∀ i d e nb, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) → Eval body nb d e →
      I (i + 1) (nextState p e))
    (hcallback : ∀ i d e nb, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) → Eval body nb d e →
      ∀ q z, q ≤ nb → Trace (compiled body p.counter p.counter) q
        (d.withPC (some (compiled body p.counter p.counter).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    {costs : List ℕ} {steps i : ℕ} {a b : State R S}
    (hvis : Visits p body costs steps a b) (hI : I i a) (hs : a.stacks p.scratch = []) :
    ∀ q z, q ≤ steps → Trace (compiled (loopCmd p body) p.counter p.counter) q
      (a.withPC (some (compiled (loopCmd p body) p.counter p.counter).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
  induction hvis generalizing i with
  | done a hf hz =>
      exact StructuredSpace.while_false_stack_bound _ _ a hf (hbound i a hI)
        _ _ _ (compiled_site _ p.counter p.counter)
  | @step a middle b nb nt costs hf hp hb hc hscratch tail ih =>
      have hbody := hcallback i a middle nb hI hs hp hb
      have hmiddle := hbody _ _ le_rfl (compiled_trace hb p.counter p.counter)
      have hpositive : 0 < value (middle.stacks p.counter) := by simpa only [hc] using hp
      have hlocal : 9 * (middle.stacks p.counter).length + 8 ≤ bound := by
        rw [hc]
        have hw := hwidth i a hI
        omega
      have hcontrol := advance_space p middle hscratch hpositive hmiddle hlocal
      have ha := advance_eval p middle hscratch
      have hsequence := StructuredSpace.sequence_stack_bound hb ha p.counter p.counter
        hbody hcontrol (compiled (.seq body (advanceCmd p)) p.counter p.counter)
        (siteAddress (.seq body (advanceCmd p))) (exitAddress (.seq body (advanceCmd p)))
        (compiled_site (.seq body (advanceCmd p)) p.counter p.counter)
      have hafter := hnext i a middle nb hI hs hp hb
      exact StructuredSpace.while_true_stack_bound hf (.seq hb ha) tail.eval
        p.counter p.counter hsequence (ih hafter (nextState_scratch p middle))
        _ _ _ (compiled_site _ p.counter p.counter)

/-- The initial restoring test and final halt preserve the same bound too. -/
theorem for_space_next {R S bound width : ℕ} (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hwidth : ∀ i d, I i d → (d.stacks p.counter).length ≤ width)
    (hbudget : 9 * width + 8 ≤ bound)
    (hnext : ∀ i d e nb, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) → Eval body nb d e →
      I (i + 1) (nextState p e))
    (hcallback : ∀ i d e nb, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) → Eval body nb d e →
      ∀ q z, q ≤ nb → Trace (compiled body p.counter p.counter) q
        (d.withPC (some (compiled body p.counter p.counter).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    {costs : List ℕ} {steps : ℕ} {a b : State R S}
    (hs : a.stacks p.scratch = [])
    (hI : I 0 (testResult p a))
    (hvis : Visits p body costs steps (testResult p a) b) :
    ∀ q z, q ≤ 8 * (a.stacks p.counter).length + 7 + steps + 1 →
      Trace (compiled (forCmd p body) p.counter p.counter) q
        (a.withPC (some (compiled (forCmd p body) p.counter p.counter).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
  have hst := testResult_stacks p a hs
  have hframe : ∀ j, (a.stacks j).length ≤ bound := by
    simpa only [hst] using hbound 0 (testResult p a) hI
  have hw : (a.stacks p.counter).length ≤ width := by
    simpa only [hst] using hwidth 0 (testResult p a) hI
  have htest := test_eval p a hs
  have hfirst := test_space p a hs hframe (by omega)
  have hloop := visits_space_next p body I hbound hwidth hbudget hnext hcallback hvis hI
    (by simpa only [hst] using hs)
  have hseq := StructuredSpace.sequence_stack_bound htest hvis.eval p.counter p.counter
    hfirst hloop (compiled (forCmd p body) p.counter p.counter)
    (siteAddress (forCmd p body)) (exitAddress (forCmd p body))
    (compiled_site (forCmd p body) p.counter p.counter)
  exact StructuredSpace.compiled_halt_stack_bound (.seq htest hvis.eval)
    p.counter p.counter hseq


/-- The actual head loop scans all `2^h` assignments with a fixed polynomial
per-visit cost, while its binary fuel retains exactly `h+1` bits. The concrete
accepted-factor command must instantiate the measured body proof. -/
theorem head_program_resources (accepted : HeadSumProgram.Code)
    (I : ℕ → HeadSumProgram.Data → Prop) (h bound cost : ℕ)
    (hcursor : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e))
    (hcallback : ∀ i d e nb, I i d → d.stacks 861 = [] →
      0 < value (d.stacks 860) → Eval (HeadSumProgram.body accepted) nb d e →
      ∀ q z, q ≤ nb →
        Trace (compiled (HeadSumProgram.body accepted) 860 860) q
          (d.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    (a : HeadSumProgram.Data) (hs : a.stacks 861 = [])
    (hi : I 0 (testResult HeadSumProgram.fuelPorts a)) :
    ∃ steps e,
      Trace (HeadSumProgram.program accepted) steps
        (a.withPC (some (HeadSumProgram.program accepted).entry)) (e.withPC none) ∧
      I (2 ^ h) e ∧ value (e.stacks 860) = 0 ∧
      (e.stacks 860).length = h + 1 ∧ e.stacks 861 = [] ∧
      steps ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) ∧
      ∀ q z, q ≤ steps → Trace (HeadSumProgram.program accepted) q
        (a.withPC (some (HeadSumProgram.program accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  have hst := testResult_stacks HeadSumProgram.fuelPorts a hs
  have hc := hcursor 0 (testResult HeadSumProgram.fuelPorts a) hi
  have hfuel : value (a.stacks 860) = 2 ^ h := by
    have hf := hc.fuel
    rw [hst] at hf
    omega
  have hwidth : (a.stacks 860).length = h + 1 := by
    simpa only [hst] using hc.fuelWidth
  obtain ⟨costs, steps, e, he, hvisit, _, hI, hz, hw, hes, hsum, ht⟩ :=
    CounterLoops.for_correct_measured_next HeadSumProgram.fuelPorts
      (HeadSumProgram.body accepted) I (fun _ => cost) spec a hs hi
  obtain ⟨loopSteps, hvis, heq⟩ := hvisit
  have hnext : ∀ i d e nb, I i d → d.stacks HeadSumProgram.fuelPorts.scratch = [] →
      0 < value (d.stacks HeadSumProgram.fuelPorts.counter) →
      Eval (HeadSumProgram.body accepted) nb d e →
      I (i + 1) (nextState HeadSumProgram.fuelPorts e) := by
    intro i d e nb hd hds hp hEval
    obtain ⟨nc, f, _, hf, _, _, hnext⟩ := spec i d hd hds hp
    have hequal : e = f := Eval.final_unique (860 : Fin 896) hEval hf
    subst f
    exact hnext
  have hspace := for_space_next HeadSumProgram.fuelPorts (HeadSumProgram.body accepted) I
    hbound (fun i d hd => (hcursor i d hd).fuelWidth.le) hbudget hnext hcallback hs hi hvis
  have htime : steps + 1 ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) := by
    simp only [HeadSumProgram.fuelPorts, budgetSum_const, hfuel, hwidth] at hsum ht
    nlinarith
  refine ⟨steps + 1, e, compiled_halt_trace he 859 853,
    by simpa only [HeadSumProgram.fuelPorts, hfuel] using hI, hz, hw.trans hwidth, hes, htime, ?_⟩
  intro q z hq hz
  apply hspace q z
  · rw [← heq]
    exact hq
  · exact hz


/-- Exact accumulator fold and all-prefix storage refer to the same head run. -/
theorem head_fold_resources (accepted : HeadSumProgram.Code)
    (visit : ℕ → List Bool → List Bool) (I : ℕ → HeadSumProgram.Data → Prop)
    (h bound cost : ℕ)
    (hcursor : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e) ∧
        e.stacks 853 = visit i (d.stacks 853))
    (hcallback : ∀ i d e nb, I i d → d.stacks 861 = [] →
      0 < value (d.stacks 860) → Eval (HeadSumProgram.body accepted) nb d e →
      ∀ q z, q ≤ nb →
        Trace (compiled (HeadSumProgram.body accepted) 860 860) q
          (d.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    (a : HeadSumProgram.Data) (hs : a.stacks 861 = [])
    (hi : I 0 (testResult HeadSumProgram.fuelPorts a)) :
    ∃ steps e,
      Trace (HeadSumProgram.program accepted) steps
        (a.withPC (some (HeadSumProgram.program accepted).entry)) (e.withPC none) ∧
      I (2 ^ h) e ∧ e.stacks 853 = HeadSumProgram.fold visit (2 ^ h) (a.stacks 853) ∧
      value (e.stacks 860) = 0 ∧ (e.stacks 860).length = h + 1 ∧ e.stacks 861 = [] ∧
      steps ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) ∧
      ∀ q z, q ≤ steps → Trace (HeadSumProgram.program accepted) q
        (a.withPC (some (HeadSumProgram.program accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  let J := fun i d => I i d ∧ d.stacks 853 = HeadSumProgram.fold visit i (a.stacks 853)
  have hstep : ∀ i d, J i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        J (i + 1) (nextState HeadSumProgram.fuelPorts e) := by
    intro i d hd hds hp
    obtain ⟨nb, e, hb, he, hc, hes, hI, hout⟩ := spec i d hd.1 hds hp
    refine ⟨nb, e, hb, he, hc, hes, hI, ?_⟩
    have hn := nextState_outside HeadSumProgram.fuelPorts e 853 (by decide) (by decide)
    rw [← hn, hout, hd.2]
    rfl
  have hstart : J 0 (testResult HeadSumProgram.fuelPorts a) := by
    refine ⟨hi, ?_⟩
    rw [testResult_stacks HeadSumProgram.fuelPorts a hs]
    rfl
  obtain ⟨steps, e, ht, hI, hz, hw, hes, htime, hspace⟩ :=
    head_program_resources accepted J h bound cost
      (fun i d hd => hcursor i d hd.1) (fun i d hd => hbound i d hd.1) hbudget hstep
      (fun i d e nb hd => hcallback i d e nb hd.1) a hs hstart
  exact ⟨steps, e, ht, hI.1, hI.2, hz, hw, hes, htime, hspace⟩


/-- Sharp composition of the actual gate, selected factor computation and
cursor increment. The concrete gate and accepted command supply local prefix
proofs; retained caller words never enter a summed-data estimate. -/
theorem body_space (accepted : HeadSumProgram.Code) {steps bound : ℕ}
    {a b : HeadSumProgram.Data} (he : Eval (HeadSumProgram.body accepted) steps a b)
    (hs : a.stacks 861 = []) (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hbudget : 9 * (a.stacks 859).length + 8 ≤ bound)
    (hgate : ∀ ng g, Eval HeadEvaluationProgram.StagedGate.command ng a g →
      g.stacks = a.stacks ∧ ∀ q z, q ≤ ng →
        Trace (compiled HeadEvaluationProgram.StagedGate.command 860 860) q
          (a.withPC (some (compiled HeadEvaluationProgram.StagedGate.command 860 860).entry)) z →
          ∀ j, (z.stacks j).length ≤ bound)
    (haccepted : ∀ g e nb, g.stacks = a.stacks → g.regs 15 = true →
      Eval accepted nb g e → e.stacks 859 = a.stacks 859 ∧ e.stacks 861 = [] ∧
      ∀ q z, q ≤ nb → Trace (compiled accepted 860 860) q
        (g.withPC (some (compiled accepted 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled (HeadSumProgram.body accepted) 860 860) q
      (a.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
  cases he with
  | @seq _ _ ng nr a g b gate rest =>
      obtain ⟨hg, hgp⟩ := hgate ng g gate
      cases rest with
      | @seq _ _ nb ni _ e _ branch increment =>
          have hbranch : e.stacks 859 = a.stacks 859 ∧ e.stacks 861 = [] ∧
              ∀ q z, q ≤ nb → Trace (compiled (.ite 15 accepted (.base .skip)) 860 860) q
                (g.withPC (some (compiled (.ite 15 accepted (.base .skip)) 860 860).entry)) z →
                ∀ j, (z.stacks j).length ≤ bound := by
            cases branch with
            | ite_true hf hacc =>
                obtain ⟨hc, hscratch, hprefix⟩ := haccepted _ _ _ hg hf hacc
                exact ⟨hc, hscratch, StructuredSpace.conditional_true_stack_bound hf hacc
                  860 860 hprefix _ _ _ (compiled_site (.ite 15 accepted (.base .skip)) 860 860)⟩
            | ite_false hf hskip =>
                cases hskip with
                | base hskip =>
                    cases hskip with
                    | skip =>
                        have hp : ∀ q z, q ≤ 0 → Trace (compiled (Cmd.base StructuredProgram.Cmd.skip) 860 860) q
                            (g.withPC (some (compiled (Cmd.base StructuredProgram.Cmd.skip) 860 860).entry)) z →
                            ∀ j, (z.stacks j).length ≤ bound := by
                          intro q z hq hz
                          have hq0 : q = 0 := by omega
                          subst q
                          cases hz
                          simpa only [StructuredProgram.State.withPC, hg] using hframe
                        exact ⟨congrFun hg 859, (congrFun hg 861).trans hs,
                          StructuredSpace.conditional_false_stack_bound hf (Eval.base (.skip g))
                            860 860 hp _ _ _
                            (compiled_site (.ite 15 accepted (.base .skip)) 860 860)⟩
          have hmiddle := hbranch.2.2 _ _ le_rfl (compiled_trace branch 860 860)
          have hincrement := Counters.increment_eval HeadSumProgram.cursorPorts e hbranch.2.1
          have hsteps := StreamResources.eval_steps_eq 860 860 increment hincrement
          have hlocal : 9 * (e.stacks HeadSumProgram.cursorPorts.counter).length + 8 ≤ bound := by
            change 9 * (e.stacks 859).length + 8 ≤ bound
            rw [hbranch.1]
            exact hbudget
          have hiprefix : ∀ q z, q ≤ ni →
              Trace (compiled (Counters.incrementCmd HeadSumProgram.cursorPorts) 860 860) q
                (e.withPC (some (compiled (Counters.incrementCmd HeadSumProgram.cursorPorts) 860 860).entry)) z →
                ∀ j, (z.stacks j).length ≤ bound := by
            intro q z hq hz
            exact ripple_space HeadSumProgram.cursorPorts true e hbranch.2.1 hmiddle hlocal
              q z (by simpa only [hsteps] using hq) hz
          have htail := StructuredSpace.sequence_stack_bound branch increment 860 860
            hbranch.2.2 hiprefix
            (compiled (.seq (.ite 15 accepted (.base .skip))
              (Counters.incrementCmd HeadSumProgram.cursorPorts)) 860 860)
            (siteAddress (.seq (.ite 15 accepted (.base .skip))
              (Counters.incrementCmd HeadSumProgram.cursorPorts)))
            (exitAddress (.seq (.ite 15 accepted (.base .skip))
              (Counters.incrementCmd HeadSumProgram.cursorPorts)))
            (compiled_site (.seq (.ite 15 accepted (.base .skip))
              (Counters.incrementCmd HeadSumProgram.cursorPorts)) 860 860)
          exact StructuredSpace.sequence_stack_bound gate (branch.seq increment) 860 860
            hgp htail (compiled (HeadSumProgram.body accepted) 860 860)
            (siteAddress (HeadSumProgram.body accepted))
            (exitAddress (HeadSumProgram.body accepted))
            (compiled_site (HeadSumProgram.body accepted) 860 860)


/-- Constructing exponential fuel scans its linear-width witness and retains
one unchanged caller envelope. -/
theorem seed_power_space (a : HeadSumProgram.Data) (bound : ℕ)
    (hf : a.stacks 860 = []) (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hbudget : 5 * (a.stacks 861).length + 5 ≤ bound) :
    ∀ q z, q ≤ 4 * (a.stacks 861).length + 5 →
      Trace (compiled HeadSumProgram.power 860 860) q
        (a.withPC (some (compiled HeadSumProgram.power 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  let p : Ports 40 896 :=
    { register := ⟨HeadSumProgram.powerRegisters, Fin.castAdd_injective 3 37⟩
      counter := 861
      scratch := 860
      counter_ne_scratch := by decide }
  have hp : (stackPorts p : Fin 2 → Fin 896) = HeadSumProgram.powerStacks := by
    funext i
    fin_cases i <;> rfl
  have hlocal : ∀ q z, q ≤ 4 * (a.stacks 861).length + 5 →
      Trace Counters.powerTwoProgram q
        ((localData (a.regs 0) (a.regs 1) (a.regs 2) (a.stacks 861) []).withPC
          (some Counters.powerTwoProgram.entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
    intro q z hq hz j
    exact (Counters.powerTwo_prefix_stack_bound (a.stacks 861) _ _ _ hq hz j).trans hbudget
  have whole := local_call_space p Counters.powerTwoProgram a _ hf
    (Counters.powerTwo_trace (a.stacks 861) (a.regs 0) (a.regs 1) (a.regs 2))
    hlocal hframe
  unfold HeadSumProgram.power
  rw [← hp]
  exact whole

open HeadEvaluationProgram.StagedGate

/-- The complete actual seed preserves one stack envelope, including an old
accumulator which is cleared by real instructions. -/
theorem seed_space {a b : HeadSumProgram.Data} {steps bound : ℕ}
    (he : Eval HeadSumProgram.seed steps a b)
    (hcursor : a.stacks 859 = []) (hfuel : a.stacks 860 = [])
    (hscratch : a.stacks 861 = []) (htemp : a.stacks 31 = [])
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hbudget : 5 * (a.stacks 651).length + 5 ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled HeadSumProgram.seed 860 860) q
      (a.withPC (some (compiled HeadSumProgram.seed 860 860).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
  let d1 := copyState a 651 859
  let d2 := copyState d1 651 861
  have h1 := copy_eval a 651 859 (by decide) (by decide) (by decide) htemp
  have s1 := copy_space 651 859 h1 (by decide) (by decide) (by decide)
    hcursor htemp hframe
  have b1 := s1 _ _ le_rfl (compiled_trace h1 860 860)
  have hd2 : d1.stacks 861 = [] := by
    simp [d1, copyState, StackRoutines.copyStacks, hscratch]
  have ht2 : d1.stacks 31 = [] := by
    simp [d1, copyState, StackRoutines.copyStacks, htemp]
  have h2 := copy_eval d1 651 861 (by decide) (by decide) (by decide) ht2
  have s2 := copy_space 651 861 h2 (by decide) (by decide) (by decide) hd2 ht2 b1
  have b2 := s2 _ _ le_rfl (compiled_trace h2 860 860)
  have hf3 : d2.stacks 860 = [] := by
    simp [d2, d1, copyState, StackRoutines.copyStacks, hfuel]
  have hw3 : d2.stacks 861 = a.stacks 651 := by
    simp [d2, d1, copyState, StackRoutines.copyStacks, hscratch]
  have h3 := HeadSumProgram.power_eval d2 hf3
  have s3 := seed_power_space d2 bound hf3 b2 (by simpa only [hw3] using hbudget)
  have b3 := s3 _ _ le_rfl (compiled_trace h3 860 860)
  have h4 := clear_eval (HeadSumProgram.powerResult d2) 853
  have s4 := clear_space 853 h4 b3
  have whole := seq_space h1 (h2.seq (h3.seq h4)) s1
    (seq_space h2 (h3.seq h4) s2 (seq_space h3 h4 s3 s4))
  have hsteps := StreamResources.eval_steps_eq 860 860 he (h1.seq (h2.seq (h3.seq h4)))
  simpa only [HeadSumProgram.seed, hsteps] using whole


/-- The native staged full-key/correction gate discharges the gate part of
the per-assignment resource contract. -/
theorem body_space_gate (accepted : HeadSumProgram.Code) {steps bound : ℕ}
    {a b : HeadSumProgram.Data} (he : Eval (HeadSumProgram.body accepted) steps a b)
    (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, a.stacks (stackMap i) = [])
    (hmatrix : a.stacks 865 = Subexp.MatrixProgramSupport.words
      (rows.map Subexp.MatrixProgramSupport.words))
    (hlen : ∀ row ∈ rows, row.length = (a.stacks 859).length)
    (hE : (a.stacks 859).length = (a.stacks 867).length)
    (hH : (a.stacks 859).length = (a.stacks 868).length)
    (hs : a.stacks 861 = []) (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hbudget : 9 * (a.stacks 859).length + 8 ≤ bound)
    (hlocal : sourceLength a + HeadEvaluationProgram.HeadGate.budget
      (a.stacks 864) (a.stacks 859) rows (a.stacks 866) + 1 ≤ bound)
    (haccepted : ∀ g e nb, g.stacks = a.stacks → g.regs 15 = true →
      Eval accepted nb g e → e.stacks 859 = a.stacks 859 ∧ e.stacks 861 = [] ∧
      ∀ q z, q ≤ nb → Trace (compiled accepted 860 860) q
        (g.withPC (some (compiled accepted 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled (HeadSumProgram.body accepted) 860 860) q
      (a.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
  apply body_space accepted he hs hframe hbudget _ haccepted
  intro ng g hEval
  obtain ⟨n, _, out, ht, _⟩ := command_eval a rows hclean hmatrix hlen hE hH
  have hEq : g = (⟨out, a.stacks⟩ : HeadSumProgram.Data) := Eval.final_unique 860 hEval ht
  have hst := congrArg (fun x : HeadSumProgram.Data => x.stacks) hEq
  exact ⟨hst,
    command_space hEval rows hclean hmatrix hlen hE hH hframe hlocal⟩


/-- Paid seed, all head assignments, and actual controller reclamation are
bounded on one trace. Initialization does not retain an assignment family. -/
theorem scan_fold_resources (accepted : HeadSumProgram.Code)
    (visit : ℕ → List Bool → List Bool) (I : ℕ → HeadSumProgram.Data → Prop)
    (h bound cost : ℕ)
    (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e) ∧
        e.stacks 853 = visit i (d.stacks 853))
    (hcallback : ∀ i d e nb, I i d → d.stacks 861 = [] →
      0 < value (d.stacks 860) → Eval (HeadSumProgram.body accepted) nb d e →
      ∀ q z, q ≤ nb → Trace (compiled (HeadSumProgram.body accepted) 860 860) q
        (d.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
    (hcursor : a.stacks 859 = []) (hfuel : a.stacks 860 = [])
    (hscratch : a.stacks 861 = []) (htemp : a.stacks 31 = [])
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hi : I 0 (testResult HeadSumProgram.fuelPorts (HeadSumProgram.seeded a))) :
    ∃ steps e,
      Trace (HeadSumProgram.scanProgram accepted) steps
        (a.withPC (some (HeadSumProgram.scanProgram accepted).entry))
        ((HeadSumProgram.finalized e).withPC none) ∧
      I (2 ^ h) e ∧
      (HeadSumProgram.finalized e).stacks 853 = HeadSumProgram.fold visit (2 ^ h) [] ∧
      (HeadSumProgram.finalized e).stacks 859 = [] ∧
      (HeadSumProgram.finalized e).stacks 860 = [] ∧
      (HeadSumProgram.finalized e).stacks 861 = [] ∧
      steps ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) + 2 * bound + 22 * h + 30 ∧
      ∀ q z, q ≤ steps → Trace (HeadSumProgram.scanProgram accepted) q
        (a.withPC (some (HeadSumProgram.scanProgram accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  have hseed := HeadSumProgram.seed_eval a h hshape hfuel hscratch htemp
  have hseedPrefix := seed_space hseed hcursor hfuel hscratch htemp hframe (by
    rw [hshape, List.length_replicate]
    omega)
  have hseedCursor := HeadSumProgram.seeded_cursor a h hshape hcursor hscratch
  have hs : (HeadSumProgram.seeded a).stacks 861 = [] := hseedCursor.scratch
  have hf : value ((HeadSumProgram.seeded a).stacks 860) = 2 ^ h := by
    have hf := hseedCursor.fuel
    omega
  have hw : ((HeadSumProgram.seeded a).stacks 860).length = h + 1 := hseedCursor.fuelWidth
  have hz0 : (HeadSumProgram.seeded a).stacks 853 = [] := by
    simp [HeadSumProgram.seeded, clearState, StackRoutines.clearStacks]
  obtain ⟨costs, nt, e, he, hvisit, hI, hout, _, _, hes, hsum, htime⟩ :=
    HeadSumProgram.command_fold accepted visit I (fun _ => cost) spec
      (HeadSumProgram.seeded a) hs hi
  obtain ⟨loopSteps, hvis, heq⟩ := hvisit
  have hnext : ∀ i d e nb, I i d → d.stacks HeadSumProgram.fuelPorts.scratch = [] →
      0 < value (d.stacks HeadSumProgram.fuelPorts.counter) →
      Eval (HeadSumProgram.body accepted) nb d e →
      I (i + 1) (nextState HeadSumProgram.fuelPorts e) := by
    intro i d e nb hd hds hp hEval
    obtain ⟨nc, f, _, hEval', _, _, hnext, _⟩ := spec i d hd hds hp
    have hequal : e = f := Eval.final_unique (860 : Fin 896) hEval hEval'
    subst f
    exact hnext
  have hloopPrefix := for_space_next HeadSumProgram.fuelPorts (HeadSumProgram.body accepted) I
    hbound (fun i d hd => (hcursorI i d hd).fuelWidth.le) hbudget hnext hcallback hs hi hvis
  have hloop : ∀ q z, q ≤ nt → Trace (compiled (HeadSumProgram.command accepted) 860 860) q
      ((HeadSumProgram.seeded a).withPC
        (some (compiled (HeadSumProgram.command accepted) 860 860).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
    intro q z hq hz
    exact hloopPrefix q z (by
      change q ≤ 8 * ((HeadSumProgram.seeded a).stacks 860).length + 7 + loopSteps + 1
      omega) hz
  have hmiddle := hloop _ _ le_rfl (compiled_trace he 860 860)
  have hfinal := HeadSumProgram.finalize_eval e
  have hfinalPrefix := HeadSumProgram.finalize_prefix hfinal hmiddle
  have htail := seq_space he hfinal hloop hfinalPrefix
  have hfull := StructuredSpace.sequence_stack_bound hseed (he.seq hfinal) 860 860
    hseedPrefix htail (HeadSumProgram.scanProgram accepted)
    (siteAddress (HeadSumProgram.scan accepted)) (exitAddress (HeadSumProgram.scan accepted))
    (compiled_site (HeadSumProgram.scan accepted) 651 853)
  have hwhole := hseed.seq (he.seq hfinal)
  have hfinalCursor := hcursorI _ e hI
  have hcursorWidth := hfinalCursor.wordWidth
  have hfuelWidth := hfinalCursor.fuelWidth
  have hloopTime : nt + 1 ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) := by
    simp only [budgetSum_const, hf, hw] at hsum htime
    nlinarith
  have hsumLength := hframe 853
  refine ⟨_, e, compiled_halt_trace hwhole 651 853,
    by simpa only [hf] using hI, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [HeadSumProgram.finalized_stacks, hf, hz0] using hout
  · simp [HeadSumProgram.finalized_stacks]
  · simp [HeadSumProgram.finalized_stacks]
  · simpa [HeadSumProgram.fuelPorts, HeadSumProgram.finalized_stacks] using hes
  · omega
  · exact StructuredSpace.compiled_halt_stack_bound hwhole 651 853 hfull

/-- Relational dictionary invariants pass through the actual complete scan.
The invariant may contain existential representations and decoded partial sums;
no canonical executable evaluator is assumed. -/
theorem scan_resources (accepted : HeadSumProgram.Code)
    (I : ℕ → HeadSumProgram.Data → Prop)
    (h bound cost : ℕ)
    (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e))
    (hcallback : ∀ i d e nb, I i d → d.stacks 861 = [] →
      0 < value (d.stacks 860) → Eval (HeadSumProgram.body accepted) nb d e →
      ∀ q z, q ≤ nb → Trace (compiled (HeadSumProgram.body accepted) 860 860) q
        (d.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
    (hcursor : a.stacks 859 = []) (hfuel : a.stacks 860 = [])
    (hscratch : a.stacks 861 = []) (htemp : a.stacks 31 = [])
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hi : I 0 (testResult HeadSumProgram.fuelPorts (HeadSumProgram.seeded a))) :
    ∃ steps e,
      Trace (HeadSumProgram.scanProgram accepted) steps
        (a.withPC (some (HeadSumProgram.scanProgram accepted).entry))
        ((HeadSumProgram.finalized e).withPC none) ∧
      I (2 ^ h) e ∧
      (HeadSumProgram.finalized e).stacks 853 = e.stacks 853 ∧
      (HeadSumProgram.finalized e).stacks 859 = [] ∧
      (HeadSumProgram.finalized e).stacks 860 = [] ∧
      (HeadSumProgram.finalized e).stacks 861 = [] ∧
      steps ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) + 2 * bound + 22 * h + 30 ∧
      ∀ q z, q ≤ steps → Trace (HeadSumProgram.scanProgram accepted) q
        (a.withPC (some (HeadSumProgram.scanProgram accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  have hseed := HeadSumProgram.seed_eval a h hshape hfuel hscratch htemp
  have hseedPrefix := seed_space hseed hcursor hfuel hscratch htemp hframe (by
    rw [hshape, List.length_replicate]
    omega)
  have hseedCursor := HeadSumProgram.seeded_cursor a h hshape hcursor hscratch
  have hs : (HeadSumProgram.seeded a).stacks 861 = [] := hseedCursor.scratch
  have hf : value ((HeadSumProgram.seeded a).stacks 860) = 2 ^ h := by
    have hf := hseedCursor.fuel
    omega
  have hw : ((HeadSumProgram.seeded a).stacks 860).length = h + 1 := hseedCursor.fuelWidth
  obtain ⟨costs, nt, e, he, hvisit, _, hI, _, _, hes, hsum, htime⟩ :=
    CounterLoops.for_correct_measured_next HeadSumProgram.fuelPorts
      (HeadSumProgram.body accepted) I (fun _ => cost) spec
      (HeadSumProgram.seeded a) hs hi
  obtain ⟨loopSteps, hvis, heq⟩ := hvisit
  change nt = 8 * ((HeadSumProgram.seeded a).stacks 860).length + 7 + loopSteps at heq
  have hnext : ∀ i d e nb, I i d → d.stacks HeadSumProgram.fuelPorts.scratch = [] →
      0 < value (d.stacks HeadSumProgram.fuelPorts.counter) →
      Eval (HeadSumProgram.body accepted) nb d e →
      I (i + 1) (nextState HeadSumProgram.fuelPorts e) := by
    intro i d e nb hd hds hp hEval
    obtain ⟨nc, f, _, hEval', _, _, hnext⟩ := spec i d hd hds hp
    have hequal : e = f := Eval.final_unique (860 : Fin 896) hEval hEval'
    subst f
    exact hnext
  have hloopPrefix := for_space_next HeadSumProgram.fuelPorts (HeadSumProgram.body accepted) I
    hbound (fun i d hd => (hcursorI i d hd).fuelWidth.le) hbudget hnext hcallback hs hi hvis
  have hloop : ∀ q z, q ≤ nt → Trace (compiled (HeadSumProgram.command accepted) 860 860) q
      ((HeadSumProgram.seeded a).withPC
        (some (compiled (HeadSumProgram.command accepted) 860 860).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
    intro q z hq hz
    exact hloopPrefix q z (by
      change q ≤ 8 * ((HeadSumProgram.seeded a).stacks 860).length + 7 + loopSteps + 1
      omega) hz
  have hmiddle := hloop _ _ le_rfl (compiled_trace he 860 860)
  have hfinal := HeadSumProgram.finalize_eval e
  have hfinalPrefix := HeadSumProgram.finalize_prefix hfinal hmiddle
  have htail := seq_space he hfinal hloop hfinalPrefix
  have hfull := StructuredSpace.sequence_stack_bound hseed (he.seq hfinal) 860 860
    hseedPrefix htail (HeadSumProgram.scanProgram accepted)
    (siteAddress (HeadSumProgram.scan accepted)) (exitAddress (HeadSumProgram.scan accepted))
    (compiled_site (HeadSumProgram.scan accepted) 651 853)
  have hwhole := hseed.seq (he.seq hfinal)
  have hfinalCursor := hcursorI _ e hI
  have hcursorWidth := hfinalCursor.wordWidth
  have hfuelWidth := hfinalCursor.fuelWidth
  have hloopTime : nt + 1 ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) := by
    simp only [HeadSumProgram.fuelPorts, budgetSum_const, hf, hw] at hsum htime
    nlinarith
  have hsumLength := hframe 853
  refine ⟨_, e, compiled_halt_trace hwhole 651 853,
    by simpa only [HeadSumProgram.fuelPorts, hf] using hI, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [HeadSumProgram.finalized_stacks]
  · simp [HeadSumProgram.finalized_stacks]
  · simp [HeadSumProgram.finalized_stacks]
  · simpa [HeadSumProgram.fuelPorts, HeadSumProgram.finalized_stacks] using hes
  · omega
  · exact StructuredSpace.compiled_halt_stack_bound hwhole 651 853 hfull

/-- The complete scan cost is a fixed polynomial factor times `2^h`. -/
theorem scan_budget_le (h bound cost : ℕ) :
    (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) + 2 * bound + 22 * h + 30 ≤
      2 ^ h * (2 * cost + 2 * bound + 54 * h + 96) := by
  have hp : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by decide)
  have hc : cost ≤ 2 ^ h * cost := by nlinarith
  have hb : bound ≤ 2 ^ h * bound := by nlinarith
  have hh : h ≤ 2 ^ h * h := by nlinarith
  nlinarith


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace
