import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawRuntime
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedSmallSAT

namespace OAI.Algorithms

/-! Finite-prefix completion for ordered clause lists. The large branch is
unchanged. The small branch is the actual ordered-input scanner, whose state
tracks clause satisfaction rather than membership in a finite word language.
The cutoff is fixed in the instruction table before any input is read. -/

namespace SubexponentialSAT.SubexpOrderedRawCompletion

open BitProgram FinitePrefixProgram
open SubexpOrderedRawPrefix (Formula encode bitLength)

variable {r s l : ℕ}

noncomputable abbrev liftedSmall (p : Program r s l) (N : ℕ) :=
  ProgramLinking.liftProgram
    (SubexpOrderedSmallSAT.smallProgram N p.inputStack p.outputStack) (scannerRegister r) id

noncomputable abbrev command (p : Program r s l) (N : ℕ) : StructuredCalls.Cmd (3 + r) s :=
  .seq (.call (liftedHeader p N))
    (.ite 0
      (.seq (.base (.atom (.set 0 false))) (.call (liftedLarge p)))
      (.call (liftedSmall p N)))

noncomputable abbrev completed (p : Program r s l) (N : ℕ) :=
  StructuredCalls.compiled (command p N) p.inputStack p.outputStack

theorem small_eval (p : BitProgram.Program r s l) (N n : ℕ) (F : Formula n)
    (hn : n < N) :
    ∃ answer, StructuredCalls.Eval (command p N)
      (Header.time N n + 3 * bitLength F + 8)
      (StructuredProgram.ioState p.inputStack (encode F))
      (StructuredProgram.ioState p.outputStack [answer]) ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  obtain ⟨answer, hsmall, hsat⟩ := SubexpOrderedSmallSAT.small_trace N n F hn p.inputStack p.outputStack
  have hh : StructuredCalls.Eval (.call (liftedHeader p N)) (Header.time N n + 1)
      (StructuredProgram.ioState p.inputStack (encode F))
      (StructuredProgram.ioState p.inputStack (encode F)) := by
    simpa [show ¬ N ≤ n by omega, SubexpOrderedRawPrefix.encode] using
      header_call p N n (SubexpOrderedRawPrefix.body F)
  have hs : StructuredCalls.Eval (.call (liftedSmall p N))
      (3 * bitLength F + 6)
      (StructuredProgram.ioState p.inputStack (encode F))
      (StructuredProgram.ioState p.outputStack [answer]) :=
    call_io (SubexpOrderedSmallSAT.smallProgram N p.inputStack p.outputStack)
      (scannerRegister r) (scannerRegister_injective r) hsmall
  have hg := StructuredCalls.Eval.ite_false (test := (0 : Fin (3 + r)))
    (yes := .seq (.base (.atom (.set 0 false))) (.call (liftedLarge p)))
    (by rfl) hs
  have h := StructuredCalls.Eval.seq hh hg
  refine ⟨answer, ?_, hsat⟩
  convert h using 1; omega

theorem completed_small (p : BitProgram.Program r s l) (N n : ℕ) (F : Formula n)
    (hn : n < N) :
    ∃ answer, BitProgram.RunsIn (completed p N)
      (6 * N + 3 * bitLength F + 12)
      (BitProgram.initial (completed p N) (encode F))
      (BitProgram.terminal (completed p N) [answer]) ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  obtain ⟨answer, he, hsat⟩ := small_eval p N n F hn
  refine ⟨answer, ⟨_, ?_, StructuredCalls.compiled_io_trace p.inputStack p.outputStack he⟩, hsat⟩
  have hb := Header.time_le N n
  omega

theorem large_eval_dirty (p : BitProgram.Program r s l) (N n : ℕ) (F : Formula n)
    (hn : N ≤ n) {steps : ℕ} {final : BitProgram.Cfg r s l}
    (hrun : BitProgram.Trace p steps (BitProgram.initial p (encode F)) final)
    (halted : final.pc = none) :
    StructuredCalls.Eval (command p N) (Header.time N n + steps + 3)
      (StructuredProgram.ioState p.inputStack (encode F)) (largeData final) := by
  have hh : StructuredCalls.Eval (.call (liftedHeader p N)) (Header.time N n + 1)
      (StructuredProgram.ioState p.inputStack (encode F))
      (ambient (r := r) p.inputStack true (encode F)) := by
    simpa [hn, SubexpOrderedRawPrefix.encode] using header_call p N n (SubexpOrderedRawPrefix.body F)
  have hb := StructuredCalls.Eval.seq (clear_flag p.inputStack (encode F))
    (large_call_dirty p hrun halted)
  have hg := StructuredCalls.Eval.ite_true (test := (0 : Fin (3 + r)))
    (no := .call (liftedSmall p N)) (by simp [ambient]) hb
  have h := StructuredCalls.Eval.seq hh hg
  convert h using 1; omega

theorem completed_large_dirty (p : BitProgram.Program r s l) (N n : ℕ) (F : Formula n)
    (hn : N ≤ n) {bound : ℕ} {final : BitProgram.Cfg r s l}
    (hrun : BitProgram.RunsIn p bound (BitProgram.initial p (encode F)) final)
    (halted : final.pc = none) :
    BitProgram.RunsIn (completed p N) (6 * N + bound + 7)
      (BitProgram.initial (completed p N) (encode F))
      ((largeData final).withPC none) := by
  obtain ⟨steps, hsteps, ht⟩ := hrun
  have h := StructuredCalls.compiled_halt_trace (large_eval_dirty p N n F hn ht halted)
    p.inputStack p.outputStack
  refine ⟨_, ?_, h⟩
  have hb := Header.time_le N n
  omega

theorem completes_eventual_dirty (p : BitProgram.Program r s l) (N width : ℕ)
    (time : ℕ → ℕ → ℕ)
    (large : ∀ n (F : Formula n), ExecSunflowerSearch.RawWidthAtMost width F → N ≤ n →
      ∃ (final : BitProgram.Cfg r s l) (answer : Bool),
        BitProgram.RunsIn p (time n (bitLength F))
          (BitProgram.initial p (encode F)) final ∧
        final.pc = none ∧ (final.stacks p.outputStack).head? = some answer ∧
        (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet F))) :
    ∀ n (F : Formula n), ExecSunflowerSearch.RawWidthAtMost width F →
      ∃ final answer, BitProgram.RunsIn (completed p N)
        (6 * N + 3 * bitLength F + time n (bitLength F) + 12)
        (BitProgram.initial (completed p N) (encode F)) final ∧
        final.pc = none ∧ (final.stacks (completed p N).outputStack).head? = some answer ∧
        (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  intro n F hwidth
  by_cases hn : N ≤ n
  · obtain ⟨final, answer, hrun, hhalted, hout, hsat⟩ := large n F hwidth hn
    refine ⟨(largeData final).withPC none, answer,
      (completed_large_dirty p N n F hn hrun hhalted).mono (by omega), rfl, ?_, hsat⟩
    exact hout
  · obtain ⟨answer, hrun, hsat⟩ := completed_small p N n F (by omega)
    refine ⟨BitProgram.terminal (completed p N) [answer], answer,
      hrun.mono (by omega), rfl, ?_, hsat⟩
    simp []

theorem primitive_completes_eventual_dirty (p : BitProgram.Program r s l) (N width : ℕ)
    (time : ℕ → ℕ → ℕ)
    (large : ∀ n (F : Formula n), ExecSunflowerSearch.RawWidthAtMost width F → N ≤ n →
      ∃ (final : BitProgram.Cfg r s l) (answer : Bool),
        BitProgram.RunsIn p (time n (bitLength F))
          (BitProgram.initial p (encode F)) final ∧
        final.pc = none ∧ (final.stacks p.outputStack).head? = some answer ∧
        (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet F))) :
    ∀ n (F : Formula n), ExecSunflowerSearch.RawWidthAtMost width F →
      ∃ answer, (BitProgram.primitive (completed p N)).OutputsInTime
        (encode F) answer
        (BitProgram.primitiveOverhead (completed p N) *
          (6 * N + 3 * bitLength F + time n (bitLength F) + 12)) ∧
        (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  intro n F hwidth
  obtain ⟨final, answer, hrun, hhalted, hout, hsat⟩ :=
    completes_eventual_dirty p N width time large n F hwidth
  exact ⟨answer, BitProgram.primitive_outputs_of_halted _ hrun hhalted hout, hsat⟩


/-- The ordered-list source contract includes every encoded order and
multiplicity, with the same finite program before all inputs. -/
abbrev ProgramDecidesWithBound (p : Program r s l) (width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ) : Prop :=
  ∀ (n : ℕ) (G : Formula n), ExecSunflowerSearch.RawWidthAtMost width G →
    ∃ (answer : Bool) (time : ℕ) (final : Cfg r s l),
      RunsIn p time (initial p (encode G)) final ∧
      final.pc = none ∧ (final.stacks p.outputStack).head? = some answer ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) ∧
      (time : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
        (bitLength G) n

abbrev DecidesAbove (p : Program r s l) (N width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ) : Prop :=
  ∀ (n : ℕ) (G : Formula n), ExecSunflowerSearch.RawWidthAtMost width G → N ≤ n →
    ∃ (answer : Bool) (time : ℕ) (final : Cfg r s l),
      RunsIn p time (initial p (encode G)) final ∧
      final.pc = none ∧ (final.stacks p.outputStack).head? = some answer ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) ∧
      (time : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
        (bitLength G) n

theorem completed_decidesWithBound (p : Program r s l) (N width : ℕ)
    {constant exponentConstant : ℝ} {degree : ℕ}
    (hc : 1 ≤ constant) (ha : 0 ≤ exponentConstant) (hd : 0 < degree)
    (large : DecidesAbove p N width constant exponentConstant degree) :
    ProgramDecidesWithBound (completed p N) width
      (((6 * N + 16 : ℕ) : ℝ) * (2 * constant)) exponentConstant degree := by
  intro n G hwidth
  by_cases hn : N ≤ n
  · obtain ⟨answer, time, final, hrun, hhalted, hout, hsat, hbound⟩ := large n G hwidth hn
    refine ⟨answer, 6 * N + 3 * bitLength G + time + 12,
      (largeData final).withPC none,
      (completed_large_dirty p N n G hn hrun hhalted).mono (by omega), rfl, hout, hsat, ?_⟩
    exact completion_overhead_le hc ha hd N _ n time hbound
  · obtain ⟨answer, hrun, hsat⟩ := completed_small p N n G (by omega)
    refine ⟨answer, 6 * N + 3 * bitLength G + 12,
      terminal (completed p N) [answer], hrun, rfl, ?_, hsat, ?_⟩
    · simp []
    · have hz : (0 : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
          (bitLength G) n := SubexpComputation.runtimeBound_nonneg (by linarith) _ _ _ _
      simpa using completion_overhead_le hc ha hd N (bitLength G) n 0
        (by simpa only [Nat.cast_zero] using hz)

def PrimitiveDecidesWithBound (machine : Computation.PrimitiveMachine) (width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ) : Prop :=
  ∀ (n : ℕ) (G : Formula n), ExecSunflowerSearch.RawWidthAtMost width G →
    ∃ (answer : Bool) (time : ℕ),
      machine.OutputsInTime (encode G) answer time ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) ∧
      (time : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
        (bitLength G) n

theorem primitive_of_program (p : Program r s l) (width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ)
    (h : ProgramDecidesWithBound p width constant exponentConstant degree) :
    PrimitiveDecidesWithBound (primitive p) width
      ((primitiveOverhead p : ℝ) * constant) exponentConstant degree := by
  intro n G hG
  obtain ⟨answer, time, final, ht, hh, ho, hs, hb⟩ := h n G hG
  refine ⟨answer, primitiveOverhead p * time, primitive_outputs_of_halted p ht hh ho, hs, ?_⟩
  rw [Nat.cast_mul, SubexpComputation.runtimeBound_mul_constant]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)

/-- This is an implication from actual eventual executions. It does not
provide the unfinished large SAT worker or its bound. The cutoff, completed
machine, and new constant are all chosen before the ordered input. -/
theorem primitive_of_eventually_bounded_program (p : Program r s l) (width : ℕ)
    {constant exponentConstant : ℝ} {degree : ℕ}
    (hc : 1 ≤ constant) (ha : 0 ≤ exponentConstant) (hd : 0 < degree)
    (large : ∀ᶠ n in Filter.atTop, ∀ G : Formula n,
      ExecSunflowerSearch.RawWidthAtMost width G →
        ∃ (answer : Bool) (time : ℕ) (final : Cfg r s l),
          RunsIn p time (initial p (encode G)) final ∧
          final.pc = none ∧ (final.stacks p.outputStack).head? = some answer ∧
          (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) ∧
          (time : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
            (bitLength G) n) :
    ∃ (N : ℕ) (newConstant : ℝ), 0 < newConstant ∧
      PrimitiveDecidesWithBound (primitive (completed p N)) width
        newConstant exponentConstant degree := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp large
  have hlarge : DecidesAbove p N width constant exponentConstant degree :=
    fun n G hG hn => hN n hn G hG
  have hdone := completed_decidesWithBound p N width hc ha hd hlarge
  refine ⟨N, (primitiveOverhead (completed p N) : ℝ) *
    (((6 * N + 16 : ℕ) : ℝ) * (2 * constant)), ?_,
    primitive_of_program (completed p N) width _ _ _ hdone⟩
  have hpos : 0 < constant := lt_of_lt_of_le (by norm_num) hc
  have hover : (0 : ℝ) < primitiveOverhead (completed p N) :=
    Nat.cast_pos.mpr (primitiveOverhead_pos _)
  positivity

/-- Instantiate the completion with the unchanged Main controller and its
actual ordered execution records. No leaf implementation is assumed to exist
merely from this conditional assembly theorem. -/
theorem complete_main_of_executions {er es : ℕ}
    (p : SubexpMainProgram.Phases er es) (leaf : SubexpMainProgram.MainCmd er es)
    (width : ℕ) {constant exponentConstant : ℝ} {degree : ℕ}
    (hc : 1 ≤ constant) (ha : 0 ≤ exponentConstant) (hd : 0 < degree)
    (large : ∀ᶠ n in Filter.atTop, ∀ G : Formula n,
      ExecSunflowerSearch.RawWidthAtMost width G →
        ∃ run : SubexpOrderedRawRuntime.Execution p leaf G,
          (run.bound : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
            (bitLength G) n) :
    ∃ (N : ℕ) (newConstant : ℝ), 0 < newConstant ∧
      PrimitiveDecidesWithBound
        (primitive (completed (SubexpMainController.program p leaf) N)) width
        newConstant exponentConstant degree := by
  apply primitive_of_eventually_bounded_program (SubexpMainController.program p leaf)
    width hc ha hd
  filter_upwards [large] with n hn
  intro G hG
  obtain ⟨run, hb⟩ := hn G hG
  obtain ⟨final, ht, hh, ho⟩ := run.runs
  exact ⟨run.records.any run.test, run.bound, final, ht, hh, ho, run.correct, hb⟩

/-- Raw identifiers are translated before the header dispatch. The original
large-input program remains the same fixed `p`. -/
noncomputable abbrev transportCommand (p : Program r s l) (N : ℕ)
    (transport : StructuredCalls.Cmd (3 + r) s) : StructuredCalls.Cmd (3 + r) s :=
  .seq transport (.call (completed p N))

noncomputable abbrev transportProgram (p : Program r s l) (N : ℕ)
    (transport : StructuredCalls.Cmd (3 + r) s) :=
  StructuredCalls.compiled (transportCommand p N transport) p.inputStack p.outputStack

/-- Exact physical composition at the external-input boundary. The actual
transport must leave only the dense input word; the completed solver may
halt with dirty work storage. Both executed halts are charged. -/
theorem transported_output (p : Program r s l) (N : ℕ)
    (transport : StructuredCalls.Cmd (3 + r) s)
    (input : List Bool) {n : ℕ} (G : Formula n) (preprocessSteps bound : ℕ)
    (preprocess : StructuredCalls.Eval transport preprocessSteps
      (StructuredProgram.ioState p.inputStack input)
      (StructuredProgram.ioState p.inputStack (encode G)))
    (final : Cfg (3 + r) s (StructuredCalls.size (command p N) + 1)) (answer : Bool)
    (hrun : RunsIn (completed p N) bound (initial (completed p N) (encode G)) final)
    (hhalt : final.pc = none) (houtput : (final.stacks p.outputStack).head? = some answer) :
    (primitive (transportProgram p N transport)).OutputsInTime input answer
      (primitiveOverhead (transportProgram p N transport) * (preprocessSteps + bound + 1)) := by
  obtain ⟨steps, hsteps, htrace⟩ := hrun
  have hfinal : (StructuredProgram.State.ofCfg final).withPC none = final := by
    rcases final with ⟨pc, regs, words⟩
    simp only at hhalt
    subst pc
    rfl
  have hcall : StructuredCalls.Eval (.call (completed p N)) steps
      (StructuredProgram.ioState p.inputStack (encode G)) (StructuredProgram.State.ofCfg final) := by
    apply StructuredCalls.Eval.call
    rw [show (StructuredProgram.ioState p.inputStack (encode G)).withPC
        (some (completed p N).entry) = initial (completed p N) (encode G) by
      apply congrArg₂ (BitProgram.Cfg.mk (some (completed p N).entry))
      · rfl
      · rfl]
    simpa only [hfinal] using htrace
  have ht : RunsIn (transportProgram p N transport) (preprocessSteps + bound + 1)
      (initial (transportProgram p N transport) input)
      ((StructuredProgram.State.ofCfg final).withPC none) := by
    refine ⟨preprocessSteps + steps + 1, by omega, ?_⟩
    exact StructuredCalls.compiled_halt_trace (preprocess.seq hcall) p.inputStack p.outputStack
  exact primitive_outputs_of_halted _ ht rfl houtput

end SubexponentialSAT.SubexpOrderedRawCompletion

end OAI.Algorithms
