import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets

/-! The actual canonical large-input run. All leaf services are constructed
internally, and the fixed program has both full physical outputs and a single
primitive trace for its time and every-prefix visited-space bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry

open BitProgram StructuredCalls DisjointReuse SqrtLog.Statement NativeOuterBudgets

theorem run (k : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∃ C A : ℝ, ∃ d S e : ℕ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F → cutoff < n →
      ∃ time : ℕ, ∃ final : LocatedCfg
        (GuardedCompiler.primitive (Native.countingProgram cutoff k (NativeLeafProgram.command k))),
        Computation.Trace
          (locatedStep (GuardedCompiler.primitive
            (Native.countingProgram cutoff k (NativeLeafProgram.command k)))) time
          (locatedInit (GuardedCompiler.primitive
            (Native.countingProgram cutoff k (NativeLeafProgram.command k)))
            (Encoding.encodeCNF F)) final ∧
        final.config.state = .inl (decide (0 < SAT.count F)) ∧
        final.config.tapes ABI.countStack =
          Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
        final.config.tapes ABI.answerStack =
          Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
        (time : ℝ) ≤ runtimeBound C A d (Encoding.formulaBitLength F) n ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ time →
          Computation.Trace
            (locatedStep (GuardedCompiler.primitive
              (Native.countingProgram cutoff k (NativeLeafProgram.command k)))) prefixSteps
            (locatedInit (GuardedCompiler.primitive
              (Native.countingProgram cutoff k (NativeLeafProgram.command k)))
              (Encoding.encodeCNF F)) intermediate →
          visitedSpace intermediate ≤ S * (Encoding.formulaBitLength F + 1) ^ e := by
  obtain ⟨Cp, _hCp, hsetup⟩ := Native.setupAfterFrontend_prepared_execution k hk
  let Ki := Cp + 1220
  obtain ⟨Cl, el, Ct, At, dt, Nleaf, hCt, hAt, _hdt, hleaf⟩ :=
    NativeLeafContract.uniform_contract k Ki 3 hk
  obtain ⟨Cg, eg, _hCg, hglobal⟩ := globalBound_polynomial k Ki 3 Cl el
  let K := Ki + Cg
  let E := 3 + eg
  obtain ⟨Cb, db, hbudget⟩ := entryTime_polynomial k K E
  obtain ⟨Cf, df, hCf, hleafTime⟩ := leafTime_runtimeBound k Cg eg Ct At hCt
    (by linarith) dt
  obtain ⟨C, hC, htime⟩ := runtime_of_tree_and_leaf k Cb db Cf At hCf (by linarith) df
  obtain ⟨S, e, hspace⟩ := primitiveSpace_polynomial K E
  obtain ⟨Ns, hs⟩ := Filter.eventually_atTop.mp
    (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 2))
  let cutoff := max 20 (max Nleaf Ns)
  refine ⟨cutoff, C, 256 + At, db + (4 * (k - 2) + 2) + df, S, e,
    hC, by linarith, ?_⟩
  intro n F hw hn
  let L := Encoding.formulaBitLength F
  let inputBound := Ki * (L + 1) ^ 3
  let bound := Cg * (L + 1) ^ eg
  let localTime := Nat.ceil (runtimeBound Ct At dt L n)
  let leafTime := NativeLeafContract.time n k localTime bound
  have hn20 : 20 ≤ n := by dsimp [cutoff] at hn; omega
  have hnleaf : Nleaf ≤ n := by dsimp [cutoff] at hn; omega
  have hscheduleTwo : 2 ≤ sparsifySchedule n := hs n (by dsimp [cutoff] at hn; omega)
  have hschedule : 1 ≤ sparsifySchedule n := by omega
  have hnL : n ≤ L := Encoding.numVariables_le_formulaBitLength F
  have hmL : F.card ≤ L := by have := Encoding.formulaBitLength_lower F; omega
  have hbody := Native.canonical_normalized_body_length F hw
  have hiK : inputBound ≤ K * (L + 1) ^ E := Nat.mul_le_mul
    (by dsimp [K]; omega) (Nat.pow_le_pow_right (by omega) (by dsimp [E]; omega))
  have hbK : bound ≤ K * (L + 1) ^ E := Nat.mul_le_mul
    (by dsimp [K]; omega) (Nat.pow_le_pow_right (by omega) (by dsimp [E]; omega))
  obtain ⟨binary, frontSteps, a, hbinary, hlen, hfrontTime, hfront, ready⟩ := Native.frontend_eval F
  obtain ⟨setupSteps, b, hsetupRun, _prepared, setupReady, hsetupTime⟩ :=
    hsetup F binary (FiniteFallback.cutoffResult a false) (ready.cutoff false)
      hbinary hlen hn20 hschedule
  have hthreshold : (b.stacks 259).length ≤ inputBound := hsetupRun.final_bound 259
  obtain ⟨hstartup, hvisit, hlocal, hclassifier, hpower⟩ :=
    hglobal n F.card L (SubexpNormalizationCorrectness.normalizedBody F).length
      inputBound (b.stacks 259).length (Cl * (L + 1) ^ el) hnL hmL hbody
      le_rfl hthreshold le_rfl
  have hcontract := hleaf n L inputBound bound hnleaf hnL le_rfl (b.stacks 259)
    setupReady.threshold hlocal hclassifier hpower
  obtain ⟨visits, outerSteps, out, houterTime, houter, hcount, hanswer, _hsat, hvisits⟩ :=
    Native.outer_from_setup k hk F hw (FiniteFallback.cutoffResult a false) b
      hsetupRun setupReady hschedule (NativeLeafProgram.command k) leafTime
      hstartup hvisit hcontract
  let sourceBound := entrySpace n L inputBound bound
  obtain ⟨hfrontBudget, hdispatchBudget, houterBudget⟩ :=
    entrySpace_requirements n L inputBound bound
  have hentry := Native.entry_large_bounded_eval
    (Native.outerCommand k (NativeLeafProgram.command k)) F binary a out hn
    hfront hfrontTime ready hlen hfrontBudget hdispatchBudget
    (DFSCountProgram.boundedEval_mono houter houterBudget)
  obtain ⟨time, final, htrace, hhalt, hcountTape, hanswerTape, hprimitiveTime, hprefix⟩ :=
    Native.counting_primitive_from_entry (NativeLeafProgram.command k) F out hentry hcount hanswer
  have hfrontPolynomial := hfrontTime.trans (Native.frontendBound_polynomial F)
  change frontSteps ≤ 4000 * (L + 1) ^ 2 at hfrontPolynomial
  change outerSteps ≤ setupSteps +
    Native.dfsTime k n (SubexpNormalizationCorrectness.normalizedBody F).length
      (b.stacks 259).length leafTime bound visits +
    12 * Native.outerBoundary inputBound bound n + 14 at houterTime
  have hmeasured : time ≤ entryTime k n L
      (SubexpNormalizationCorrectness.normalizedBody F).length (b.stacks 259).length
      leafTime inputBound bound visits setupSteps := by
    dsimp [entryTime]
    omega
  have hsetupK : setupSteps ≤ K * (L + 1) ^ E := by
    apply le_trans (Nat.le_succ setupSteps |>.trans hsetupTime)
    apply le_trans (Nat.mul_le_mul_right ((L + 1) ^ 3) (show Cp ≤ Ki by dsimp [Ki]; omega)) hiK
  have hpoly := hbudget n L (SubexpNormalizationCorrectness.normalizedBody F).length
    (b.stacks 259).length leafTime inputBound bound visits setupSteps hnL hbody
    (hthreshold.trans hiK) hiK hbK hsetupK
  have hleafReal : (leafTime : ℝ) ≤ runtimeBound Cf At df L n :=
    hleafTime n L bound hnL le_rfl
  have htotal := htime n L visits leafTime time hn20 hschedule hnL hvisits hleafReal
    (hmeasured.trans hpoly)
  refine ⟨time, final, htrace, hhalt, hcountTape, hanswerTape, htotal, ?_⟩
  intro t z ht hz
  exact (hprefix t z ht hz).trans (hspace n L inputBound bound hnL hiK hbK)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry
