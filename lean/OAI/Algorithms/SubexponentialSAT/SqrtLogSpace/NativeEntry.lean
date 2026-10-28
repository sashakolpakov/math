import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeFrontend
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback

/-! The canonical frontend and actual fixed-cutoff dispatcher share one finite
program. The large command is supplied by the subsequent concrete integration. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

noncomputable def entryCommand (cutoff : ℕ) (large : Cmd 80 1220) : Cmd 80 1220 :=
  .seq frontendCommand (FiniteFallback.dispatchCommand cutoff large)

noncomputable def entryProgram (cutoff : ℕ) (large : Cmd 80 1220) :=
  compiled (entryCommand cutoff large) ABI.countStack ABI.answerStack

theorem FrontendReady.cutoff {n : ℕ} {F : SAT.CNF (Fin n)} {binary : List Bool}
    {a : State 80 1220} (ready : FrontendReady F binary a) (flag : Bool) :
    FrontendReady F binary (FiniteFallback.cutoffResult a flag) := by
  constructor
  · exact (FiniteFallback.cutoffResult_frame a flag _ (by decide) (by decide)).trans ready.input
  · exact (FiniteFallback.cutoffResult_frame a flag _ (by decide) (by decide)).trans ready.header
  · exact (FiniteFallback.cutoffResult_frame a flag _ (by decide) (by decide)).trans ready.body
  · exact (FiniteFallback.cutoffResult_frame a flag _ (by decide) (by decide)).trans ready.dimension
  · intro i hc hu hb hn
    by_cases hw : i = 270
    · subst i
      exact FiniteFallback.cutoffResult_work a flag
    by_cases hs : i = 271
    · subst i
      exact FiniteFallback.cutoffResult_scratch a flag
    exact (FiniteFallback.cutoffResult_frame a flag i hw hs).trans (ready.blank i hc hu hb hn)

/-- Small inputs run the actual finite counting table and positivity scan after
the paid canonical frontend, retaining the ambient variable universe. -/
theorem entry_small_eval {cutoff n : ℕ} (large : Cmd 80 1220)
    (F : SAT.CNF (Fin n)) (hn : n ≤ cutoff) :
    ∃ steps b, Eval (entryCommand cutoff large) steps
        (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b ∧
      b.stacks ABI.countStack = countWord (SAT.count F) ∧
      b.stacks ABI.answerStack = [decide (0 < SAT.count F)] ∧
      steps + 1 ≤ 4100 * (Encoding.formulaBitLength F + 1) ^ 2 := by
  obtain ⟨binary, steps, a, _, _, ht, he, ready⟩ := frontend_eval F
  have hdispatch := FiniteFallback.dispatch_small_eval large F hn a ready.header ready.input
  have h270 := ready.blank 270 (by decide) (by decide) (by decide) (by decide)
  have h271 := ready.blank 271 (by decide) (by decide) (by decide) (by decide)
  have ha := ready.blank ABI.answerStack (by decide) (by decide) (by decide) (by decide)
  have hs := ready.blank ABI.positivityScratch (by decide) (by decide) (by decide) (by decide)
  rw [h270, h271, ha, hs] at hdispatch
  refine ⟨_, _, he.seq hdispatch, FiniteFallback.framedResult_count _ _, ?_, ?_⟩
  · rw [FiniteFallback.framedResult_answer, countWord_toNat]
  · have hfront := ht.trans (frontendBound_polynomial F)
    have hword := countWord_count_length F
    have hnL := Encoding.numVariables_le_formulaBitLength F
    simp only [List.length_nil] at *
    nlinarith

theorem entry_small_trace {cutoff n : ℕ} (large : Cmd 80 1220)
    (F : SAT.CNF (Fin n)) (hn : n ≤ cutoff) :
    ∃ (steps : ℕ) (b : State 80 1220), Trace (entryProgram cutoff large) steps
        (initial (entryProgram cutoff large) (Encoding.encodeCNF F)) (b.withPC none) ∧
      b.stacks ABI.countStack = countWord (SAT.count F) ∧
      b.stacks ABI.answerStack = [decide (0 < SAT.count F)] ∧
      steps ≤ 4100 * (Encoding.formulaBitLength F + 1) ^ 2 ∧
      ∀ prefixSteps c, prefixSteps ≤ steps →
        Trace (entryProgram cutoff large) prefixSteps
          (initial (entryProgram cutoff large) (Encoding.encodeCNF F)) c →
        ∀ i, (c.stacks i).length ≤
          Encoding.formulaBitLength F + 4100 * (Encoding.formulaBitLength F + 1) ^ 2 := by
  obtain ⟨steps, b, he, hc, ha, ht⟩ := entry_small_eval large F hn
  refine ⟨steps + 1, b, compiled_halt_trace he ABI.countStack ABI.answerStack, hc, ha, ht, ?_⟩
  intro prefixSteps c hp htrace i
  exact StructuredSpace.local_stack_bound (entryProgram cutoff large)
    (steps := 4100 * (Encoding.formulaBitLength F + 1) ^ 2)
    (show dataBits (initial (entryProgram cutoff large) (Encoding.encodeCNF F)) ≤
      Encoding.formulaBitLength F by simp [Encoding.formulaBitLength])
    prefixSteps c (hp.trans ht) htrace i

/-- The actual small branch of the unified program produces both physical
outputs on the same primitive run, with all-prefix visited-cell space. -/
theorem entry_small_primitive {cutoff n : ℕ} (large : Cmd 80 1220)
    (F : SAT.CNF (Fin n)) (hn : n ≤ cutoff) :
    ∃ time : ℕ, ∃ final : LocatedCfg (GuardedCompiler.primitive (entryProgram cutoff large)),
      Computation.Trace (locatedStep (GuardedCompiler.primitive (entryProgram cutoff large)))
        time (locatedInit (GuardedCompiler.primitive (entryProgram cutoff large))
          (Encoding.encodeCNF F)) final ∧
      final.config.state = .inl (decide (0 < SAT.count F)) ∧
      final.config.tapes ABI.countStack =
        Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
      final.config.tapes ABI.answerStack =
        Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
      time ≤ 28700 * (Encoding.formulaBitLength F + 1) ^ 2 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace
          (locatedStep (GuardedCompiler.primitive (entryProgram cutoff large))) prefixSteps
          (locatedInit (GuardedCompiler.primitive (entryProgram cutoff large))
            (Encoding.encodeCNF F)) intermediate →
        visitedSpace intermediate ≤ 1220 * (2 * Encoding.formulaBitLength F +
          4100 * (Encoding.formulaBitLength F + 1) ^ 2 + 15) := by
  obtain ⟨steps, b, htrace, hcount, hanswer, htime, hspace⟩ := entry_small_trace large F hn
  obtain ⟨time, ht, final, hrun, hhalt, hc, ha, hs⟩ :=
    CompileSpace.compile_word_answer_space (entryProgram cutoff large) ABI.countStack
      htrace rfl hcount hanswer hspace
  refine ⟨time, final, hrun, hhalt, hc, ha, ?_, ?_⟩
  · calc
      time ≤ 7 * steps := ht
      _ ≤ 7 * (4100 * (Encoding.formulaBitLength F + 1) ^ 2) :=
        Nat.mul_le_mul_left 7 htime
      _ = _ := by ring
  · intro prefixSteps intermediate hp htr
    have h := hs prefixSteps intermediate hp htr
    change visitedSpace intermediate ≤ 1220 *
      (Encoding.formulaBitLength F + 4100 * (Encoding.formulaBitLength F + 1) ^ 2 +
        Encoding.formulaBitLength F + 15) at h
    convert h using 1
    ring

theorem entry_large_eval {cutoff n frontSteps steps : ℕ} (large : Cmd 80 1220)
    (F : SAT.CNF (Fin n)) (binary : List Bool) (a b : State 80 1220)
    (hn : cutoff < n)
    (hfront : Eval frontendCommand frontSteps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) a)
    (ready : FrontendReady F binary a)
    (hlarge : Eval large steps (FiniteFallback.cutoffResult a false) b) :
    Eval (entryCommand cutoff large) (frontSteps + (10 * n + 29 + steps))
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b := by
  have hd := FiniteFallback.dispatch_large_eval large hn a b ready.header hlarge
  rw [ready.blank 270 (by decide) (by decide) (by decide) (by decide),
    ready.blank 271 (by decide) (by decide) (by decide) (by decide)] at hd
  simpa only [entryCommand, List.length_nil, Nat.mul_zero, Nat.zero_add] using hfront.seq hd

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
