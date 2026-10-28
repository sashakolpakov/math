import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateContextRefinement

namespace OAI.Algorithms

/-!
# Concrete inputs and score bytes for the global score builder

The sequential controller's memory invariant determines the assignment,
width, and processed-index stacks. Its high-stack invariant supplies the
encoded alphabet, depth, raw pair plans, and seed tables. These literal
equalities instantiate both inputs of the fixed score builder.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderInput

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

/-- The preparation context reads the actual processed counter bytes. -/
def preparationContext (vertices : List V) (factors : List E) (pairs : List (V × V))
    (d : ScoreBuilderProgram.Data) : PairPreparationProgram.Context where
  seedCount := (AssignmentEnumeration.seedIndices vertices factors Δ).length
  processedBits := d.stacks 19
  pairs := pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)

/-- The candidate scorer receives the exact pair table produced by preparation. -/
def context (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (n : ℕ) (pairs : List (V × V))
    (d : ScoreBuilderProgram.Data) : CandidateScoreProgram.Context :=
  let pre := preparationContext P slots vertices factors pairs d
  CandidateScoreRefinement.candidateContext (Δ := Δ) alphabet default fixed n
    (d.stacks 10) (d.stacks 19)
    (PairPreparationProgram.selectedPairs pre.seedCount pre.processedBits.length pre.pairs)

/-- All persistent high-stack inputs are explicit encodings. -/
def environment (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (pairs : List (V × V)) : Fin 48 → List Bool :=
  let M := (AssignmentEnumeration.seedIndices vertices factors Δ).length
  ScoreBuilderProgram.environment
    (ProgramEncoding.encodeRecords (alphabet.map ReadPlan.encodeWord))
    (List.replicate (2 * (Δ + 1)) true)
    (PairScoreProgram.pairRecords
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (PairPreparationProgram.seedBytes M) (SelectionTableProgram.unary M)

omit [Fintype V] [NeZero r] in
private theorem preparation_input_of_memory (default : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (fixed : List (Word r Q))
    (n : ℕ) (pairs : List (V × V)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (environment P slots (default :: tail) vertices factors pairs) d.stacks) :
    ∀ i, (PairPreparationProgram.inputState (preparationContext P slots vertices factors pairs d) d.regs).stacks i =
      d.stacks (ScoreBuilderProgram.preparationPorts i) := by
  dsimp only [SequentialProgram.HighState] at hh
  intro i
  by_cases hi : 20 ≤ (ScoreBuilderProgram.preparationPorts i).val
  · rw [hh _ hi]
    fin_cases i <;> first
    | exact absurd hi (by decide)
    | simp [PairPreparationProgram.inputState, preparationContext,
        ScoreBuilderProgram.preparationPorts, environment, ScoreBuilderProgram.environment]
  · fin_cases i <;> first
    | exact absurd hi (by decide)
    | (solve
        | simp [PairPreparationProgram.inputState, preparationContext,
            ScoreBuilderProgram.preparationPorts]
        | (simp [PairPreparationProgram.inputState, preparationContext,
            ScoreBuilderProgram.preparationPorts]
           exact hm.scratch _ (by decide)))

omit [Fintype V] [NeZero r] in
private theorem candidate_input_of_memory (default : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (fixed : List (Word r Q))
    (n : ℕ) (pairs : List (V × V)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (environment P slots (default :: tail) vertices factors pairs) d.stacks) :
    ∀ i, (CandidateScoreProgram.inputState (context P slots (default :: tail) vertices factors default fixed n pairs d) (fun _ => false)).stacks i =
      (ScoreBuilderProgram.prepared (preparationContext P slots vertices factors pairs d) d).stacks
        (ScoreBuilderProgram.candidatePorts i) := by
  dsimp only [SequentialProgram.HighState] at hh
  intro i
  simp only [ScoreBuilderProgram.prepared]
  by_cases h40 : ScoreBuilderProgram.candidatePorts i = 40
  · rw [h40, Function.update_self]
    fin_cases i <;> first
    | exact absurd h40 (by decide)
    | simp [CandidateScoreProgram.inputState, CandidateScoreProgram.baseState,
        CandidateScoreProgram.workState, ScoreBuilderProgram.preparedBytes,
        context, preparationContext, CandidateScoreRefinement.candidateContext]
  · rw [Function.update_of_ne h40]
    by_cases hi : 20 ≤ (ScoreBuilderProgram.candidatePorts i).val
    · rw [hh _ hi]
      fin_cases i <;> first
      | exact absurd h40 (by decide)
      | exact absurd hi (by decide)
      | simp [CandidateScoreProgram.inputState, CandidateScoreProgram.baseState,
          CandidateScoreProgram.workState, ScoreBuilderProgram.candidatePorts,
          context, preparationContext, CandidateScoreRefinement.candidateContext,
          environment, ScoreBuilderProgram.environment]
    · fin_cases i <;> first
      | exact absurd h40 (by decide)
      | exact absurd hi (by decide)
      | (solve
          | simp [CandidateScoreProgram.inputState, CandidateScoreProgram.baseState,
              CandidateScoreProgram.workState, CandidateScoreProgram.original,
              ScoreBuilderProgram.candidatePorts, context, preparationContext,
              CandidateScoreRefinement.candidateContext, hm.assignment,
              List.flatten_append, List.replicate_succ, List.map_replicate]
          | (simp [CandidateScoreProgram.inputState, CandidateScoreProgram.baseState,
              CandidateScoreProgram.workState, CandidateScoreProgram.original,
              ScoreBuilderProgram.candidatePorts, context, preparationContext,
              CandidateScoreRefinement.candidateContext, List.map_replicate]
             exact hm.scratch _ (by decide)))

omit [Fintype V] [NeZero r] in
/-- The two subroutine input conditions follow from the actual memory and high-stack invariants. -/
theorem inputFor_of_memory (default : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (fixed : List (Word r Q))
    (n : ℕ) (pairs : List (V × V)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (environment P slots (default :: tail) vertices factors pairs) d.stacks) :
    ScoreBuilderProgram.InputFor (preparationContext P slots vertices factors pairs d)
      (context P slots (default :: tail) vertices factors default fixed n pairs d) d := by
  exact ⟨preparation_input_of_memory P slots default tail vertices factors fixed n pairs d hm hh,
    candidate_input_of_memory P slots default tail vertices factors fixed n pairs d hm hh⟩

omit [Fintype V] [NeZero r] in
theorem context_pairs (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (n : ℕ) (pairs : List (V × V))
    (d : ScoreBuilderProgram.Data)
    (hp : (d.stacks 19).length = fixed.length)
    (hsize : n + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    (context P slots alphabet vertices factors default fixed n pairs d).pairs =
      pairs.map (CandidateScoreRefinement.selectedPairPlans P slots vertices factors
        (fixed.length + 1) n) := by
  dsimp [context, CandidateScoreRefinement.candidateContext, preparationContext]
  rw [hp]
  exact CandidateScoreRefinement.prepared_pairs_eq P slots vertices factors fixed.length n pairs
    (by omega)

omit [Fintype V] [NeZero r] in
theorem candidate_valid_of_memory (default : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (pairs : List (V × V)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    (context P slots (default :: tail) vertices factors default fixed n pairs d).Valid := by
  have hw : (d.stacks 10).length = ReadPlan.wordWidth r Q := by
    simpa only [ReadPlan.encodeWord_length] using hm.width
  have hp := context_pairs P slots (default :: tail) vertices factors default fixed n pairs d
    hm.processed hsize
  exact CandidateScoreRefinement.candidateContext_valid P slots (default :: tail)
    vertices factors hv he default fixed n (d.stacks 10) (d.stacks 19) _ pairs
    hw hm.processed hsize hp

omit [Fintype V] [NeZero r] in
/-- The actual emitted score bytes equal the sequential controller's exact
natural objective, in the original alphabet order. -/
theorem scoreBytes_eq (default : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (pairs : List (V × V)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hpairs : pairs.Perm (vertices.product vertices)) :
    ScoreBuilderProgram.scoreBytes
      (context P slots (default :: tail) vertices factors default fixed n pairs d) =
    ProgramEncoding.encodeRecords ((default :: tail).map (fun candidate => UnaryCompare.encode
      (NaturalAssignment.sequentialNumerator P slots (default :: tail) vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) default n (candidate :: fixed)))) := by
  have hw : (d.stacks 10).length = ReadPlan.wordWidth r Q := by
    simpa only [ReadPlan.encodeWord_length] using hm.width
  have hp := context_pairs P slots (default :: tail) vertices factors default fixed n pairs d
    hm.processed hsize
  exact congrArg ProgramEncoding.encodeRecords
    (CandidateScoreRefinement.candidateContext_scoreRecords P slots (default :: tail)
      vertices factors hv he default fixed n (d.stacks 10) (d.stacks 19) _ pairs
      hw hsize hp hpairs)

end SubexponentialSAT.Subexp.ScoreBuilderInput

end OAI.Algorithms
