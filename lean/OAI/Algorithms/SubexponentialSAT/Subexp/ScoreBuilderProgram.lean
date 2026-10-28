import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderPorts
import OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram

namespace OAI.Algorithms

/-!
# The actual global candidate-score builder

Pair read plans are prepared once for the current processed position. The
candidate loop then executes the local collision enumeration and emits scores
in candidate order. A final fixed routine restores the temporary table ports.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderProgram

open BitProgram StructuredCalls

abbrev preparation : Cmd 16 48 := .call
  (ProgramLinking.liftProgram PairPreparationProgram.program id preparationPorts)

abbrev candidates : Cmd 16 48 := .call
  (ProgramLinking.liftProgram CandidateScoreProgram.program id candidatePorts)

abbrev command : Cmd 16 48 := .seq preparation (.seq candidates finish)
abbrev program : Program 16 48 (size command + 1) := compiled command 8 0

def preparedBytes (pre : PairPreparationProgram.Context) : List Bool :=
  PairScoreProgram.pairRecords (PairPreparationProgram.selectedPairs
    pre.seedCount pre.processedBits.length pre.pairs)

def scoreBytes (ctx : CandidateScoreProgram.Context) : List Bool :=
  ProgramEncoding.encodeRecords (CandidateScoreProgram.scoreRecords ctx)

def prepared (pre : PairPreparationProgram.Context) (d : Data) : Data :=
  ⟨fun _ => false, Function.update d.stacks 40 (preparedBytes pre)⟩

def scored (pre : PairPreparationProgram.Context) (ctx : CandidateScoreProgram.Context)
    (d : Data) (regs : Fin 16 → Bool) : Data :=
  ⟨regs, Function.update (prepared pre d).stacks 41 (scoreBytes ctx)⟩

/-- Exact encoded inputs for the two fixed subroutines. These are equalities
of runtime stack contents; no execution or mathematical score is assumed. -/
structure InputFor (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (d : Data) : Prop where
  preparation : ∀ i,
    (PairPreparationProgram.inputState pre d.regs).stacks i = d.stacks (preparationPorts i)
  candidates : ∀ i,
    (CandidateScoreProgram.inputState ctx (fun _ => false)).stacks i =
      (prepared pre d).stacks (candidatePorts i)

def resultState (d : Data) (regs : Fin 16 → Bool) (scores : List Bool) : Data :=
  ⟨regs, Function.update d.stacks 0 scores⟩

def sourceBudget (pre : PairPreparationProgram.Context) (ctx : CandidateScoreProgram.Context) : ℕ :=
  PairPreparationProgram.traceBound pre + CandidateScoreProgram.sourceBudget ctx +
    6 * (scoreBytes ctx).length + 2 * (preparedBytes pre).length + 10

theorem preparation_eval (pre : PairPreparationProgram.Context) (d : Data)
    (hinput : ∀ i, (PairPreparationProgram.inputState pre d.regs).stacks i =
      d.stacks (preparationPorts i)) :
    ∃ n ≤ PairPreparationProgram.traceBound pre,
      Eval preparation n d (prepared pre d) := by
  obtain ⟨n, hn, ht⟩ := PairPreparationProgram.program_runsIn pre d.regs
  have hout : (PairPreparationProgram.outputState pre).stacks =
      Function.update (PairPreparationProgram.inputState pre d.regs).stacks 29 (preparedBytes pre) := by
    rfl
  have he := call_lifted_update PairPreparationProgram.program preparationPorts
    preparationPorts_injective d (PairPreparationProgram.inputState pre d.regs)
    (PairPreparationProgram.outputState pre) 29 (preparedBytes pre) rfl hinput hout ht
  exact ⟨n, hn, by
    simpa [preparation, prepared, preparationPorts,
      PairPreparationProgram.outputState] using he⟩

theorem candidates_eval (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (hc : ctx.Valid) (d : Data)
    (hinput : ∀ i, (CandidateScoreProgram.inputState ctx (fun _ => false)).stacks i =
      (prepared pre d).stacks (candidatePorts i)) :
    ∃ n ≤ CandidateScoreProgram.sourceBudget ctx, ∃ regs,
      Eval candidates n (prepared pre d) (scored pre ctx d regs) := by
  obtain ⟨regs, n, hn, ht⟩ := CandidateScoreProgram.program_run ctx hc (fun _ => false)
  have hout : (CandidateScoreProgram.outputState ctx regs).stacks =
      Function.update (CandidateScoreProgram.inputState ctx (fun _ => false)).stacks 32
        (scoreBytes ctx) := by
    rfl
  have he := call_lifted_update CandidateScoreProgram.program candidatePorts candidatePorts_injective
    (prepared pre d) (CandidateScoreProgram.inputState ctx (fun _ => false))
    (CandidateScoreProgram.outputState ctx regs) 32 (scoreBytes ctx) rfl hinput hout ht
  exact ⟨n, hn, regs, by
    simpa [candidates, scored, candidatePorts,
      CandidateScoreProgram.outputState] using he⟩

theorem command_eval (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (hc : ctx.Valid) (d : Data) (hi : InputFor pre ctx d) :
    ∃ n ≤ sourceBudget pre ctx - 1, ∃ regs,
      Eval command n d (resultState d regs (scoreBytes ctx)) := by
  obtain ⟨a, ha, hpre⟩ := preparation_eval pre d hi.preparation
  obtain ⟨b, hb, regs, hcan⟩ := candidates_eval pre ctx hc d hi.candidates
  have h0 : d.stacks 0 = [] := by
    simpa [PairPreparationProgram.inputState, preparationPorts] using (hi.preparation 0).symm
  have h40 : d.stacks 40 = [] := by
    simpa [PairPreparationProgram.inputState, preparationPorts] using (hi.preparation 29).symm
  have h41 : d.stacks 41 = [] := by
    simpa [PairPreparationProgram.inputState, preparationPorts] using (hi.preparation 25).symm
  have h42 : d.stacks 42 = [] := by
    simpa [PairPreparationProgram.inputState, preparationPorts] using (hi.preparation 26).symm
  have hfinish := finish_eval (scored pre ctx d regs)
    (by simp [scored, prepared, h0]) (by simp [scored, prepared, h42])
  have hend : finished (scored pre ctx d regs) =
      resultState d (readRegs regs 0 1 none) (scoreBytes ctx) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases h0j : j = 0
      · subst j; simp [ scored, prepared]
      by_cases h40j : j = 40
      · subst j; simp [ scored, prepared, h40]
      by_cases h41j : j = 41
      · subst j; simp [ scored, prepared, h41]
      by_cases h42j : j = 42
      · subst j; simp [ scored, prepared, h42]
      · simp [ scored, prepared, h0j, h40j, h41j, h42j]
  rw [hend] at hfinish
  refine ⟨a + (b + (6 * (scoreBytes ctx).length + 2 * (preparedBytes pre).length + 9)),
    ?_, readRegs regs 0 1 none, ?_⟩
  · unfold sourceBudget
    omega
  · have he := hpre.seq (hcan.seq hfinish)
    simpa [command, scored, prepared] using he

theorem program_run (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (hc : ctx.Valid) (d : Data) (hi : InputFor pre ctx d) :
    ∃ regs, RunsIn program (sourceBudget pre ctx)
      (d.withPC (some program.entry)) ((resultState d regs (scoreBytes ctx)).withPC none) := by
  obtain ⟨n, hn, regs, he⟩ := command_eval pre ctx hc d hi
  refine ⟨regs, n + 1, ?_, compiled_halt_trace he 8 0⟩
  have hp : 0 < sourceBudget pre ctx := by unfold sourceBudget; omega
  omega

theorem primitive_run (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (hc : ctx.Valid) (d : Data) (hi : InputFor pre ctx d) :
    ∃ regs, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * sourceBudget pre ctx)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program ((resultState d regs (scoreBytes ctx)).withPC none)) := by
  obtain ⟨regs, hr⟩ := program_run pre ctx hc d hi
  exact ⟨regs, primitive_execution program hr⟩

end SubexponentialSAT.Subexp.ScoreBuilderProgram

end OAI.Algorithms
