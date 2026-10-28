import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderInputBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRawInput
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRawRefinement

namespace OAI.Algorithms

/-! The same physical size bound holds for the generated raw-plan order. -/

namespace SubexponentialSAT.Subexp.ScoreBuilderRawInputBounds

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

omit [Fintype V] [NeZero r] in
theorem boundedInputs_of_memory (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (rawPlans : List PairScoreProgram.PlanPair)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices))
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    ScoreBuilderBounds.BoundedInputs
      (ScoreBuilderRawInput.preparationContext
        (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans d)
      (ScoreBuilderRawInput.context Δ (a :: tail) a fixed n
        (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans d)
      (ScoreBuilderInputBounds.inputBound (AssignmentEnumeration.seedIndices vertices factors Δ).length
        vertices.length (a :: tail).length (ReadPlan.wordWidth r Q) Δ) := by
  have h := ScoreBuilderInputBounds.boundedInputs_of_memory P slots a tail vertices factors hv he
    fixed n pairs hpairs d hm hsize
  refine ⟨h.seedCount, h.processed, ?_, ?_, h.original, h.before,
    h.width, h.depth, h.candidates⟩
  · change rawPlans.length ≤ _
    rw [hraw.length_eq]
    exact h.pairCount
  · intro pair hp
    exact h.pairPayload pair (hraw.mem_iff.mp hp)

omit [Fintype V] [NeZero r] in
theorem sourceBudget_le (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (rawPlans : List PairScoreProgram.PlanPair)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices))
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    ScoreBuilderProgram.sourceBudget
      (ScoreBuilderRawInput.preparationContext
        (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans d)
      (ScoreBuilderRawInput.context Δ (a :: tail) a fixed n
        (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans d) ≤
      ScoreBuilderInputBounds.stepBound (AssignmentEnumeration.seedIndices vertices factors Δ).length
        vertices.length (a :: tail).length (ReadPlan.wordWidth r Q) Δ := by
  have hc := ScoreBuilderRawInput.candidate_valid_of_memory P slots a tail vertices factors hv he
    fixed n rawPlans pairs d hm hsize hraw
  have hb := boundedInputs_of_memory P slots a tail vertices factors hv he fixed n
    rawPlans pairs hpairs hraw d hm hsize
  have h := ScoreBuilderBounds.sourceBudget_le _ _ hc _ hb
    (by simp [ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext]) rfl
  simpa only [ScoreBuilderInputBounds.stepBound, ScoreBuilderRawInput.context,
    CandidateScoreRefinement.candidateContext, List.length_map, List.length_replicate] using h

omit [Fintype V] in
theorem sourceBudget_le_polynomial (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (rawPlans : List PairScoreProgram.PlanPair)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices))
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    ScoreBuilderProgram.sourceBudget
      (ScoreBuilderRawInput.preparationContext
        (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans d)
      (ScoreBuilderRawInput.context Δ (a :: tail) a fixed n
        (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans d) ≤
      (10000 * 31 ^ 6 * 1025 ^ 12) *
        ScoreBuilderSizeBounds.sourceSize vertices.length factors.length
          (blockSize r Q Δ) Q r Δ ^ 50 :=
  (sourceBudget_le P slots a tail vertices factors hv he fixed n rawPlans pairs
    hpairs hraw d hm hsize).trans
      (ScoreBuilderInputBounds.stepBound_le_polynomial a tail haNodup haFull vertices factors)

omit [Fintype V] [NeZero r] in
theorem cost_le (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (rawPlans : List PairScoreProgram.PlanPair)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices))
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    ScoreBuilderRawRefinement.cost (Δ := Δ) a tail vertices factors rawPlans fixed n d ≤
      ScoreBuilderInputBounds.stepBound (AssignmentEnumeration.seedIndices vertices factors Δ).length
        vertices.length (a :: tail).length (ReadPlan.wordWidth r Q) Δ :=
  sourceBudget_le P slots a tail vertices factors hv he fixed n rawPlans pairs hpairs hraw d hm hsize

omit [Fintype V] in
theorem cost_le_polynomial (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (rawPlans : List PairScoreProgram.PlanPair)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices))
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    ScoreBuilderRawRefinement.cost (Δ := Δ) a tail vertices factors rawPlans fixed n d ≤
      (10000 * 31 ^ 6 * 1025 ^ 12) *
        ScoreBuilderSizeBounds.sourceSize vertices.length factors.length
          (blockSize r Q Δ) Q r Δ ^ 50 :=
  sourceBudget_le_polynomial P slots a tail haNodup haFull vertices factors hv he
    fixed n rawPlans pairs hpairs hraw d hm hsize

omit [Fintype V] [NeZero r] in
theorem refines (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (rawPlans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (hpairs : pairs.Perm (vertices.product vertices)) :
    SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
      (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) a)
      ScoreBuilderProgram.command
      (ScoreBuilderInputBounds.stepBound (AssignmentEnumeration.seedIndices vertices factors Δ).length
        vertices.length (a :: tail).length (ReadPlan.wordWidth r Q) Δ)
      (AssignmentEnumeration.seedIndices vertices factors Δ).length
      (ScoreBuilderRawInput.environment Δ (a :: tail)
        (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans) := by
  apply ScoreBuilderRawRefinement.refines_of_cost_bound P slots a tail vertices factors hv he
    rawPlans pairs hraw hpairs
  intro n fixed d hsize hm _
  exact cost_le P slots a tail vertices factors hv he fixed n rawPlans pairs hpairs hraw d hm hsize

end SubexponentialSAT.Subexp.ScoreBuilderRawInputBounds

end OAI.Algorithms
