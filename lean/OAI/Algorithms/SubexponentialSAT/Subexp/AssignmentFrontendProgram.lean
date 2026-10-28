import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentPairFrontend
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.InitializedRawAssignmentProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRawInputBounds

namespace OAI.Algorithms

/-!
# Assignment from encoded scopes and runtime parameters

The same finite program first constructs all incidence-plan pairs, then the
word alphabet and seed range, and finally initializes and runs conditional
expectation. The mathematical witnesses below name the order actually emitted
by those producers. They do not enter the instruction table.
-/

namespace SubexponentialSAT.Subexp.AssignmentFrontendProgram

open BitProgram StructuredCalls MulticolorTypes

abbrev Data := State 16 48

abbrev command : Cmd 16 48 :=
  .seq (.call AssignmentPairFrontend.program)
    (.seq (.call AssignmentInputProgram.program)
      (.call InitializedRawAssignmentProgram.program))

abbrev program : Program 16 48 (size command + 1) := compiled command 6 8

def scoreBound (r Q Δ D E : ℕ) : ℕ :=
  ScoreBuilderInputBounds.stepBound (E + (Δ + 1) * D) D (r ^ Q) (Q * r) Δ

def assignmentBudget (r Q Δ D E : ℕ) (pairBits : List Bool) : ℕ :=
  let M := E + (Δ + 1) * D
  AssignmentInitProgram.sourceCost (AssignmentInputProgram.context r Q Δ D E pairBits) +
    (M * (scoreBound r Q Δ D E + SequentialProgram.selectionBudget (r ^ Q)
      (D ^ 2 * (blockSize r Q Δ) ^ 2) M (Q * r) + 3) + 3) + 1

def sourceBudget (r Q Δ D : ℕ) (scopes : List (List ℕ)) : ℕ :=
  let bits := AssignmentPairFrontend.pairBytes D Δ scopes
  AssignmentPairFrontend.sourceBudget D Δ scopes +
    (AssignmentInputProgram.budget r Q Δ D scopes.length bits + 1) +
    assignmentBudget r Q Δ D scopes.length bits + 1

/-- The persistent input tables are ready for packing and row construction
after the assignment loop finishes. -/
def RuntimeReady (ctx : AssignmentInitProgram.Context) (e : Data) : Prop :=
  e.stacks 9 = ctx.packedAlphabet ∧
  (e.stacks 10).length = ctx.width.length ∧
  e.stacks 11 = [] ∧
  (∀ j ∈ SequentialProgram.scratchPorts, e.stacks j = []) ∧
  SequentialProgram.HighState
    (ScoreBuilderProgram.environment ctx.alphabetRecords ctx.depth ctx.rawPairs
      ctx.seedRecords (AssignmentInitProgram.unary ctx.seedCount)) e.stacks

private theorem context_ext (a b : AssignmentInitProgram.Context)
    (h0 : a.defaultWord = b.defaultWord) (h1 : a.packedAlphabet = b.packedAlphabet)
    (h2 : a.alphabetRecords = b.alphabetRecords) (h3 : a.width = b.width)
    (h4 : a.depth = b.depth) (h5 : a.rawPairs = b.rawPairs)
    (h6 : a.seedRecords = b.seedRecords) (h7 : a.seedCount = b.seedCount) : a = b := by
  cases a
  cases b
  simp_all

/-- Numeric incidence plans denote the precise slot map used by the semantic
assignment theorem, including the generated vertex and factor orders. -/
theorem canonicalPairs_eq (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    SubexpVertexPairProgram.canonicalPairs D Δ scopes =
      ((List.finRange D).product (List.finRange D)).map
        (CandidateScoreRefinement.rawPairPlans (IncidencePlanSpec.pattern D scopes)
          (IncidencePlanSpec.slots D Δ scopes hd)
          (List.finRange D) (List.finRange scopes.length)) := by
  simp only [SubexpVertexPairProgram.canonicalPairs, ← List.range_eq_range',
    ← List.map_coe_finRange, List.product, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, CandidateScoreRefinement.rawPairPlans,
    IncidencePlanSpec.vertexPlan_eq_readPlan D Δ scopes hd]

/-- The generated alphabet and seed bytes are exactly a valid initializer
context. Alphabet order remains the producer's actual order. -/
theorem inputContext_eq (r Q Δ D : ℕ) (scopes : List (List ℕ))
    (a : Word r Q) (tail : List (Word r Q)) (rawPlans : List PairScoreProgram.PlanPair)
    (hrows : AssignmentAlphabetSemantics.wordBytes r Q =
      (a :: tail).map ReadPlan.encodeWord)
    (hpairs : SubexpVertexPairProgram.pairRows D Δ scopes =
      rawPlans.map PairScoreProgram.pairBytes) :
    AssignmentInputProgram.context r Q Δ D scopes.length
      (AssignmentPairFrontend.pairBytes D Δ scopes) =
    InitializedRawAssignmentProgram.initialContext (Δ := Δ) a tail
      (List.finRange D) (List.finRange scopes.length) rawPlans := by
  apply context_ext
  all_goals simp only [AssignmentInputProgram.context,
    InitializedRawAssignmentProgram.initialContext, hrows, List.map_cons,
    List.headD_cons, ReadPlan.encodeWord_length, ReadPlan.wordWidth,
    AssignmentPairFrontend.pairBytes, hpairs, PairScoreProgram.pairRecords,
    AssignmentSeedRange.seedRecords, PairPreparationProgram.seedBytes,
    AssignmentEnumeration.seedIndices_length, List.length_finRange,
    AssignmentInputProgram.seedCount, AssignmentInputProgram.unary]
  all_goals rfl

/-- Literal execution composition. All three calls are fixed, already
specified programs; the input contains only scopes and unary parameters. -/
theorem run_of_assignment (regs : Fin 16 → Bool) (r Q Δ D : ℕ)
    (scopes : List (List ℕ)) (hr : 0 < r)
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (B : ℕ) (e : Data)
    (ha : RunsIn InitializedRawAssignmentProgram.program B
      ((AssignmentInputProgram.outputState r Q Δ D scopes.length
        (AssignmentPairFrontend.pairBytes D Δ scopes)).withPC
          (some InitializedRawAssignmentProgram.program.entry)) (e.withPC none)) :
    RunsIn program
      (AssignmentPairFrontend.sourceBudget D Δ scopes +
        (AssignmentInputProgram.budget r Q Δ D scopes.length
          (AssignmentPairFrontend.pairBytes D Δ scopes) + 1) + B + 1)
      ((AssignmentPairFrontend.inputState regs r Q Δ D scopes).withPC (some program.entry))
      (e.withPC none) := by
  obtain ⟨rf, p, hp, ht⟩ := AssignmentPairFrontend.program_run regs r Q Δ D scopes hd
  obtain ⟨q, hq, hqrun⟩ := AssignmentInputProgram.program_runsIn rf r Q Δ D scopes.length
    (AssignmentPairFrontend.pairBytes D Δ scopes) hr
  obtain ⟨s, hs, hsrun⟩ := ha
  have h := (Eval.call AssignmentPairFrontend.program ht).seq
    ((Eval.call AssignmentInputProgram.program hqrun).seq
      (Eval.call InitializedRawAssignmentProgram.program hsrun))
  refine ⟨p + (q + s) + 1, by omega, ?_⟩
  exact compiled_halt_trace h 6 8

/-- Complete assignment execution from raw scopes. No prepared alphabet,
pair-plan table, seed table, score stream, or execution callback is assumed. -/
theorem program_run_framed (regs : Fin 16 → Bool) (r Q Δ D : ℕ) [NeZero r]
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ a : Word r Q, ∃ tail : List (Word r Q), ∃ e : Data,
      (a :: tail).Nodup ∧ (∀ w, w ∈ a :: tail) ∧
      (a :: tail).map ReadPlan.encodeWord = AssignmentAlphabetSemantics.wordBytes r Q ∧
      RunsIn program (sourceBudget r Q Δ D scopes)
        ((AssignmentPairFrontend.inputState regs r Q Δ D scopes).withPC (some program.entry))
        (e.withPC none) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues
        (IncidencePlanSpec.pattern D scopes) (IncidencePlanSpec.slots D Δ scopes hd)
        a tail (List.finRange D)
        (AssignmentEnumeration.seedIndices (List.finRange D)
          (List.finRange scopes.length) Δ)).reverse.map ReadPlan.encodeWord).flatten ∧
      RuntimeReady (AssignmentInputProgram.context r Q Δ D scopes.length
        (AssignmentPairFrontend.pairBytes D Δ scopes)) e := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  obtain ⟨a, tail, hwords, hnodup, hfull⟩ :=
    AssignmentAlphabetSemantics.wordBytes_order hr Q
  obtain ⟨rawPlans, hrawBytes, hraw⟩ := SubexpVertexPairProgram.rawPlans_exists D Δ scopes
  rw [canonicalPairs_eq D Δ scopes hd] at hraw
  have hctx := inputContext_eq r Q Δ D scopes a tail rawPlans hwords.symm hrawBytes
  have hlen : (a :: tail).length = r ^ Q := by
    have h := congrArg List.length hwords
    simpa only [List.length_map, AssignmentAlphabetSemantics.wordBytes_length] using h
  let P := IncidencePlanSpec.pattern D scopes
  let slots := IncidencePlanSpec.slots D Δ scopes hd
  let vertices := List.finRange D
  let factors := List.finRange scopes.length
  let pairs := vertices.product vertices
  have hcost : ∀ n fixed (d : ScoreBuilderProgram.Data),
      n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length →
      SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks →
      SequentialProgram.HighState
        (ScoreBuilderRawInput.environment Δ (a :: tail)
          (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans) d.stacks →
      ScoreBuilderRawRefinement.cost (Δ := Δ) a tail vertices factors rawPlans fixed n d ≤
        scoreBound r Q Δ D scopes.length := by
    intro n fixed d hsize hm _
    have h := ScoreBuilderRawInputBounds.cost_le P slots a tail vertices factors
      (fun v => List.mem_finRange v) (fun f => List.mem_finRange f)
      fixed n rawPlans pairs (List.Perm.refl _) hraw d hm hsize
    simpa only [scoreBound, vertices, factors, AssignmentEnumeration.seedIndices_length,
      List.length_finRange, hlen, ReadPlan.wordWidth] using h
  obtain ⟨e, he, hmemory, hremaining, hhigh⟩ :=
    InitializedRawAssignmentProgram.program_run_framed P slots a tail
    hnodup hfull vertices factors (fun v => List.mem_finRange v)
    (fun f => List.mem_finRange f) rawPlans pairs hraw (List.Perm.refl _)
    (scoreBound r Q Δ D scopes.length) hcost (fun _ => false)
  have hb : InitializedRawAssignmentProgram.sourceBudget (Δ := Δ) a tail vertices factors
      rawPlans (scoreBound r Q Δ D scopes.length) =
      assignmentBudget r Q Δ D scopes.length (AssignmentPairFrontend.pairBytes D Δ scopes) := by
    unfold InitializedRawAssignmentProgram.sourceBudget assignmentBudget
    rw [← hctx]
    simp only [vertices, factors, AssignmentEnumeration.seedIndices_length,
      List.length_finRange, hlen, ReadPlan.encodeWord_length, ReadPlan.wordWidth]
  rw [hb] at he
  have ha : RunsIn InitializedRawAssignmentProgram.program
      (assignmentBudget r Q Δ D scopes.length (AssignmentPairFrontend.pairBytes D Δ scopes))
      ((AssignmentInputProgram.outputState r Q Δ D scopes.length
        (AssignmentPairFrontend.pairBytes D Δ scopes)).withPC
          (some InitializedRawAssignmentProgram.program.entry)) (e.withPC none) := by
    simpa only [AssignmentInputProgram.outputState, hctx] using he
  refine ⟨a, tail, e, hnodup, hfull, hwords,
    run_of_assignment regs r Q Δ D scopes hr hd _ e ha, ?_, ?_⟩
  · simpa only [List.replicate_zero, List.append_nil] using hmemory.assignment
  · rw [hctx]
    refine ⟨hmemory.alphabet, ?_, hremaining, hmemory.scratch, hhigh⟩
    simpa only [InitializedRawAssignmentProgram.initialContext, List.length_replicate]
      using hmemory.width

theorem program_run (regs : Fin 16 → Bool) (r Q Δ D : ℕ) [NeZero r]
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ a : Word r Q, ∃ tail : List (Word r Q), ∃ e : Data,
      (a :: tail).Nodup ∧ (∀ w, w ∈ a :: tail) ∧
      RunsIn program (sourceBudget r Q Δ D scopes)
        ((AssignmentPairFrontend.inputState regs r Q Δ D scopes).withPC (some program.entry))
        (e.withPC none) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues
        (IncidencePlanSpec.pattern D scopes) (IncidencePlanSpec.slots D Δ scopes hd)
        a tail (List.finRange D)
        (AssignmentEnumeration.seedIndices (List.finRange D)
          (List.finRange scopes.length) Δ)).reverse.map ReadPlan.encodeWord).flatten := by
  obtain ⟨a, tail, e, hn, hf, _, hr, ho, _⟩ := program_run_framed regs r Q Δ D scopes hd
  exact ⟨a, tail, e, hn, hf, hr, ho⟩

theorem primitive_run (regs : Fin 16 → Bool) (r Q Δ D : ℕ) [NeZero r]
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ a : Word r Q, ∃ tail : List (Word r Q), ∃ e : Data,
      (a :: tail).Nodup ∧ (∀ w, w ∈ a :: tail) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * sourceBudget r Q Δ D scopes)
        (primitiveCfg program ((AssignmentPairFrontend.inputState regs r Q Δ D scopes).withPC
          (some program.entry))) (primitiveCfg program (e.withPC none)) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues
        (IncidencePlanSpec.pattern D scopes) (IncidencePlanSpec.slots D Δ scopes hd)
        a tail (List.finRange D)
        (AssignmentEnumeration.seedIndices (List.finRange D)
          (List.finRange scopes.length) Δ)).reverse.map ReadPlan.encodeWord).flatten := by
  obtain ⟨a, tail, e, hn, hf, hr, ho⟩ := program_run regs r Q Δ D scopes hd
  exact ⟨a, tail, e, hn, hf, primitive_execution program hr, ho⟩

end SubexponentialSAT.Subexp.AssignmentFrontendProgram

end OAI.Algorithms
