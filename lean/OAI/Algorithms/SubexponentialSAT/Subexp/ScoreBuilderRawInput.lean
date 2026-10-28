import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderInput
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidatePlanPermutation

namespace OAI.Algorithms

/-!
# Score-builder inputs from physically generated raw pair plans

The runtime pair table is retained in its actual generated order. A
permutation proof connects that order to the mathematical vertex-pair list;
the code never decodes plans back to vertex identifiers.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderRawInput

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

def preparationContext (seedCount : ℕ) (rawPlans : List PairScoreProgram.PlanPair)
    (d : ScoreBuilderProgram.Data) : PairPreparationProgram.Context where
  seedCount := seedCount
  processedBits := d.stacks 19
  pairs := rawPlans

def context {r Q : ℕ} (Δ : ℕ) (alphabet : List (Word r Q))
    (default : Word r Q) (fixed : List (Word r Q)) (n seedCount : ℕ)
    (rawPlans : List PairScoreProgram.PlanPair) (d : ScoreBuilderProgram.Data) :
    CandidateScoreProgram.Context :=
  CandidateScoreRefinement.candidateContext (Δ := Δ) alphabet default fixed n
    (d.stacks 10) (d.stacks 19)
    (PairPreparationProgram.selectedPairs seedCount (d.stacks 19).length rawPlans)

def environment {r Q : ℕ} (Δ : ℕ) (alphabet : List (Word r Q))
    (seedCount : ℕ) (rawPlans : List PairScoreProgram.PlanPair) : Fin 48 → List Bool :=
  ScoreBuilderProgram.environment
    (ProgramEncoding.encodeRecords (alphabet.map ReadPlan.encodeWord))
    (List.replicate (2 * (Δ + 1)) true)
    (PairScoreProgram.pairRecords rawPlans)
    (PairPreparationProgram.seedBytes seedCount) (SelectionTableProgram.unary seedCount)

private theorem preparation_input_of_memory {r Q : ℕ} (Δ : ℕ) (default : Word r Q)
    (tail fixed : List (Word r Q)) (n seedCount : ℕ)
    (rawPlans : List PairScoreProgram.PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState (environment Δ (default :: tail) seedCount rawPlans)
      d.stacks) :
    ∀ i, (PairPreparationProgram.inputState (preparationContext seedCount rawPlans d) d.regs).stacks i =
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
    | (simp [PairPreparationProgram.inputState, preparationContext,
        ScoreBuilderProgram.preparationPorts] <;>
        (apply hm.scratch ; decide))

private theorem candidate_input_of_memory {r Q : ℕ} (Δ : ℕ) (default : Word r Q)
    (tail fixed : List (Word r Q)) (n seedCount : ℕ)
    (rawPlans : List PairScoreProgram.PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState (environment Δ (default :: tail) seedCount rawPlans)
      d.stacks) :
    ∀ i, (CandidateScoreProgram.inputState (context Δ (default :: tail) default fixed n seedCount rawPlans d) (fun _ => false)).stacks i =
      (ScoreBuilderProgram.prepared (preparationContext seedCount rawPlans d) d).stacks
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
          context, CandidateScoreRefinement.candidateContext,
          environment, ScoreBuilderProgram.environment]
    · fin_cases i <;> first
      | exact absurd h40 (by decide)
      | exact absurd hi (by decide)
      | (simp [CandidateScoreProgram.inputState, CandidateScoreProgram.baseState,
          CandidateScoreProgram.workState, CandidateScoreProgram.original,
          ScoreBuilderProgram.candidatePorts, context,
          CandidateScoreRefinement.candidateContext, hm.assignment, List.flatten_append,
          List.replicate_succ, List.map_replicate] <;>
          (apply hm.scratch ; decide))

/-- The two subroutine input conditions follow from the actual memory and high-stack invariants. -/
theorem inputFor_of_memory {r Q : ℕ} (Δ : ℕ) (default : Word r Q)
    (tail fixed : List (Word r Q)) (n seedCount : ℕ)
    (rawPlans : List PairScoreProgram.PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState (environment Δ (default :: tail) seedCount rawPlans)
      d.stacks) :
    ScoreBuilderProgram.InputFor (preparationContext seedCount rawPlans d)
      (context Δ (default :: tail) default fixed n seedCount rawPlans d) d := by
  exact ⟨preparation_input_of_memory Δ default tail fixed n seedCount rawPlans d hm hh,
    candidate_input_of_memory Δ default tail fixed n seedCount rawPlans d hm hh⟩

section Semantic

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

omit [Fintype V] [NeZero r] in
theorem context_pairs_perm (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (default : Word r Q) (fixed : List (Word r Q)) (n : ℕ)
    (rawPlans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (d : ScoreBuilderProgram.Data) (hp : (d.stacks 19).length = fixed.length)
    (hsize : n + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors))) :
    (context Δ alphabet default fixed n
      (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans d).pairs.Perm
      (pairs.map (CandidateScoreRefinement.selectedPairPlans P slots vertices factors
        (fixed.length + 1) n)) := by
  dsimp [context, CandidateScoreRefinement.candidateContext]
  rw [hp]
  exact CandidateScoreRefinement.prepared_pairs_perm P slots vertices factors fixed.length n
    rawPlans pairs (by omega) hraw

omit [Fintype V] [NeZero r] in
theorem candidate_valid_of_memory (default : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (rawPlans : List PairScoreProgram.PlanPair)
    (pairs : List (V × V)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors))) :
    (context Δ (default :: tail) default fixed n
      (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans d).Valid := by
  have hw : (d.stacks 10).length = ReadPlan.wordWidth r Q := by
    simpa only [ReadPlan.encodeWord_length] using hm.width
  have hp := context_pairs_perm P slots (default :: tail) vertices factors default fixed n
    rawPlans pairs d hm.processed hsize hraw
  exact CandidateScoreRefinement.candidateContext_valid_perm P slots (default :: tail)
    vertices factors hv he default fixed n (d.stacks 10) (d.stacks 19) _ pairs
    hw hm.processed hsize hp

omit [Fintype V] [NeZero r] in
/-- Raw pair order changes neither candidate order nor the exact natural
score encoded by the physical candidate loop. -/
theorem scoreBytes_eq (default : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (rawPlans : List PairScoreProgram.PlanPair)
    (pairs : List (V × V)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (hpairs : pairs.Perm (vertices.product vertices)) :
    ScoreBuilderProgram.scoreBytes
      (context Δ (default :: tail) default fixed n
        (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans d) =
      ProgramEncoding.encodeRecords ((default :: tail).map (fun candidate => UnaryCompare.encode
        (NaturalAssignment.sequentialNumerator P slots (default :: tail) vertices
          (AssignmentEnumeration.seedIndices vertices factors Δ) default n (candidate :: fixed)))) := by
  have hw : (d.stacks 10).length = ReadPlan.wordWidth r Q := by
    simpa only [ReadPlan.encodeWord_length] using hm.width
  have hp := context_pairs_perm P slots (default :: tail) vertices factors default fixed n
    rawPlans pairs d hm.processed hsize hraw
  exact congrArg ProgramEncoding.encodeRecords
    (CandidateScoreRefinement.candidateContext_scoreRecords_perm P slots (default :: tail)
      vertices factors hv he default fixed n (d.stacks 10) (d.stacks 19) _ pairs
      hw hsize hp hpairs)

end Semantic

end SubexponentialSAT.Subexp.ScoreBuilderRawInput

end OAI.Algorithms
