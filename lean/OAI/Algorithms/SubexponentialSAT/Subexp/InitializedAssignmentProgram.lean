import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRefinement

namespace OAI.Algorithms

/-!
# Initializing and running the fixed conditional-expectation program

This joins the physical initial-array construction to the physical score and
minimum loop. The input record producers remain separately composable stages.
-/

namespace SubexponentialSAT.Subexp.InitializedAssignmentProgram

open BitProgram StructuredCalls MulticolorTypes SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

def initialContext (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (pairs : List (V × V)) :
    AssignmentInitProgram.Context where
  defaultWord := ReadPlan.encodeWord a
  packedAlphabet := ((a :: tail).map ReadPlan.encodeWord).flatten
  alphabetRecords := ProgramEncoding.encodeRecords ((a :: tail).map ReadPlan.encodeWord)
  width := List.replicate (ReadPlan.encodeWord a).length true
  depth := List.replicate (2 * (Δ + 1)) true
  rawPairs := PairScoreProgram.pairRecords
    (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors))
  seedRecords := PairPreparationProgram.seedBytes
    (AssignmentEnumeration.seedIndices vertices factors Δ).length
  seedCount := (AssignmentEnumeration.seedIndices vertices factors Δ).length

abbrev command : Cmd 16 48 :=
  .seq (.call AssignmentInitProgram.program) (.call ScoreBuilderRefinement.assignmentProgram)

abbrev program : Program 16 48 (size command + 1) := compiled command 0 8

/-- The completed controller retains all runtime tables and exposes its full
memory invariant for the next construction stage. -/
theorem run_of_refines_framed {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (ctx : AssignmentInitProgram.Context)
    (env : Fin 48 → List Bool) (scoreBound valueBound : ℕ)
    (hword : ctx.defaultWord = encode a)
    (halphabet : ctx.packedAlphabet = ((a :: tail).map encode).flatten)
    (hwidthCtx : ctx.width.length = (encode a).length)
    (henv : ScoreBuilderProgram.environment ctx.alphabetRecords ctx.depth ctx.rawPairs
      ctx.seedRecords (AssignmentInitProgram.unary ctx.seedCount) = env)
    (hwidth : ∀ x, (encode x).length = (encode a).length)
    (hscore : ∀ n fixed x, n + 1 + fixed.length ≤ ctx.seedCount → x ∈ a :: tail →
      evaluate n (x :: fixed) ≤ valueBound)
    (hbuilder : SequentialProgram.ScoreBuilderRefines encode a tail evaluate
      ScoreBuilderProgram.command scoreBound ctx.seedCount env)
    (regs : Fin 16 → Bool) :
    ∃ e : SequentialProgram.Data,
      RunsIn program
        (AssignmentInitProgram.sourceCost ctx +
          (ctx.seedCount * (scoreBound + SequentialProgram.selectionBudget
            (a :: tail).length valueBound ctx.seedCount (encode a).length + 3) + 3) + 1)
        ((AssignmentInitProgram.inputState ctx regs).withPC (some program.entry))
        (e.withPC none) ∧
      SequentialProgram.Memory encode a tail 0
        (NaturalAssignment.assignNat a tail evaluate ctx.seedCount []) e.stacks ∧
      e.stacks 11 = [] ∧ SequentialProgram.HighState env e.stacks := by
  let ready := AssignmentInitProgram.outputState ctx
  have hm := AssignmentInitProgram.output_memory encode a tail ctx hword halphabet hwidthCtx
  have hh : SequentialProgram.HighState env ready.stacks := by
    rw [← henv]
    exact AssignmentInitProgram.output_highState ctx
  have hstep := SequentialProgram.stepRefines_of_scoreBuilder encode a tail evaluate
    ScoreBuilderProgram.command scoreBound valueBound ctx.seedCount env hwidth hscore hbuilder
  obtain ⟨t, ht, e, he, hem, hec, heh⟩ := SequentialProgram.loop_eval encode a tail evaluate
    ScoreBuilderProgram.command
    (scoreBound + SequentialProgram.selectionBudget
      (a :: tail).length valueBound ctx.seedCount (encode a).length)
    ctx.seedCount env hstep ctx.seedCount [] ready (by simp) hm
    (AssignmentInitProgram.output_remaining ctx) hh
  have hcontroller := compiled_halt_trace ((SequentialProgram.peek_eval ready).seq he) 8 8
  have hi := AssignmentInitProgram.program_trace ctx regs
  have hc := (Eval.call AssignmentInitProgram.program hi).seq
    (Eval.call ScoreBuilderRefinement.assignmentProgram hcontroller)
  refine ⟨e, ⟨AssignmentInitProgram.sourceCost ctx + (1 + t + 1) + 1,
    by omega, ?_⟩, hem, hec, heh⟩
  simpa only [program, command, ready, ScoreBuilderRefinement.assignmentProgram] using
    compiled_halt_trace hc 0 8

/-- Reusable composition rule for the fixed initializer and fixed controller.
The caller supplies a proved refinement of the actual score-builder code. -/
theorem run_of_refines {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (ctx : AssignmentInitProgram.Context)
    (env : Fin 48 → List Bool) (scoreBound valueBound : ℕ)
    (hword : ctx.defaultWord = encode a)
    (halphabet : ctx.packedAlphabet = ((a :: tail).map encode).flatten)
    (hwidthCtx : ctx.width.length = (encode a).length)
    (henv : ScoreBuilderProgram.environment ctx.alphabetRecords ctx.depth ctx.rawPairs
      ctx.seedRecords (AssignmentInitProgram.unary ctx.seedCount) = env)
    (hwidth : ∀ x, (encode x).length = (encode a).length)
    (hscore : ∀ n fixed x, n + 1 + fixed.length ≤ ctx.seedCount → x ∈ a :: tail →
      evaluate n (x :: fixed) ≤ valueBound)
    (hbuilder : SequentialProgram.ScoreBuilderRefines encode a tail evaluate
      ScoreBuilderProgram.command scoreBound ctx.seedCount env)
    (regs : Fin 16 → Bool) :
    ∃ e : SequentialProgram.Data,
      RunsIn program
        (AssignmentInitProgram.sourceCost ctx +
          (ctx.seedCount * (scoreBound + SequentialProgram.selectionBudget
            (a :: tail).length valueBound ctx.seedCount (encode a).length + 3) + 3) + 1)
        ((AssignmentInitProgram.inputState ctx regs).withPC (some program.entry))
        (e.withPC none) ∧
      e.stacks 8 = ((NaturalAssignment.assignNat a tail evaluate ctx.seedCount []).reverse.map
        encode).flatten := by
  obtain ⟨e, he, hm, _, _⟩ := run_of_refines_framed encode a tail evaluate ctx env
    scoreBound valueBound hword halphabet hwidthCtx henv hwidth hscore hbuilder regs
  exact ⟨e, he, by simpa only [List.replicate_zero, List.append_nil] using hm.assignment⟩

def sourceBudget (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (pairs : List (V × V)) (scoreBound : ℕ) : ℕ :=
  let M := (AssignmentEnumeration.seedIndices vertices factors Δ).length
  AssignmentInitProgram.sourceCost (initialContext P slots a tail vertices factors pairs) +
    (M * (scoreBound + SequentialProgram.selectionBudget (a :: tail).length
      (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) M
      (ReadPlan.encodeWord a).length + 3) + 3) + 1

omit [Fintype V] [NeZero r] in
/-- Actual initialization followed by the actual fixed assignment loop.
The only quantitative premise is a bound on the already specified physical
score-builder cost. -/
theorem program_run (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices)) (B : ℕ)
    (hcost : ∀ n fixed (d : ScoreBuilderProgram.Data),
      n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length →
      SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks →
      SequentialProgram.HighState
        (ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs) d.stacks →
      ScoreBuilderRefinement.cost P slots a tail vertices factors pairs fixed n d ≤ B)
    (regs : Fin 16 → Bool) :
    ∃ e : SequentialProgram.Data,
      RunsIn program (sourceBudget P slots a tail vertices factors pairs B)
        ((AssignmentInitProgram.inputState
          (initialContext P slots a tail vertices factors pairs) regs).withPC
            (some program.entry)) (e.withPC none) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues P slots a tail vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ)).reverse.map
          ReadPlan.encodeWord).flatten := by
  let ctx := initialContext P slots a tail vertices factors pairs
  let ready := AssignmentInitProgram.outputState ctx
  have hm : SequentialProgram.Memory ReadPlan.encodeWord a tail ctx.seedCount [] ready.stacks :=
    AssignmentInitProgram.output_memory ReadPlan.encodeWord a tail ctx rfl rfl
      (by simp [ctx, initialContext])
  have hh : SequentialProgram.HighState
      (ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs) ready.stacks := by
    simpa only [ready, ctx, initialContext, ScoreBuilderInput.environment,
      AssignmentInitProgram.unary, SelectionTableProgram.unary] using
        AssignmentInitProgram.output_highState ctx
  have hb := ScoreBuilderRefinement.refines_of_cost_bound P slots a tail
    vertices factors hv he pairs hpairs B hcost
  have hs : ∀ n fixed x,
      n + 1 + fixed.length ≤ ctx.seedCount → x ∈ a :: tail →
      NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) a n (x :: fixed) ≤
          vertices.length ^ 2 * (blockSize r Q Δ) ^ 2 := by
    intro n fixed x hsize _
    exact NaturalAssignment.sequentialNumerator_le P slots (a :: tail) haNodup haFull
      vertices (AssignmentEnumeration.seedIndices vertices factors Δ) a n (x :: fixed)
  obtain ⟨e, ⟨t, ht, heval⟩, hout⟩ := SequentialProgram.program_of_scoreBuilder
    ReadPlan.encodeWord a tail
    (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices
      (AssignmentEnumeration.seedIndices vertices factors Δ) a)
    ScoreBuilderProgram.command B (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2)
    ctx.seedCount (ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs)
    (by intro x; simp [ReadPlan.encodeWord_length]) hs hb ready hm
    (AssignmentInitProgram.output_remaining ctx) hh
  have hi := AssignmentInitProgram.program_trace ctx regs
  have hc := (Eval.call AssignmentInitProgram.program hi).seq
    (Eval.call ScoreBuilderRefinement.assignmentProgram heval)
  refine ⟨e, ⟨AssignmentInitProgram.sourceCost ctx + t + 1, ?_, ?_⟩, ?_⟩
  · exact Nat.add_le_add_right
      (Nat.add_le_add_left ht (AssignmentInitProgram.sourceCost ctx)) 1
  · simpa only [program, command, ready, ctx,
      ScoreBuilderRefinement.assignmentProgram] using compiled_halt_trace hc 0 8
  · simpa only [NaturalAssignment.naturalValues, ctx, initialContext] using hout

omit [Fintype V] [NeZero r] in
theorem primitive_run (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices)) (B : ℕ)
    (hcost : ∀ n fixed (d : ScoreBuilderProgram.Data),
      n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length →
      SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks →
      SequentialProgram.HighState
        (ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs) d.stacks →
      ScoreBuilderRefinement.cost P slots a tail vertices factors pairs fixed n d ≤ B)
    (regs : Fin 16 → Bool) :
    ∃ e : SequentialProgram.Data,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * sourceBudget P slots a tail vertices factors pairs B)
        (primitiveCfg program ((AssignmentInitProgram.inputState
          (initialContext P slots a tail vertices factors pairs) regs).withPC
            (some program.entry))) (primitiveCfg program (e.withPC none)) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues P slots a tail vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ)).reverse.map
          ReadPlan.encodeWord).flatten := by
  obtain ⟨e, hr, hout⟩ := program_run P slots a tail haNodup haFull vertices factors hv he
    pairs hpairs B hcost regs
  exact ⟨e, primitive_execution program hr, hout⟩

end SubexponentialSAT.Subexp.InitializedAssignmentProgram

end OAI.Algorithms
