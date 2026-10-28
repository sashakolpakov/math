import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCompletionGenerated
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramInputs

namespace OAI.Algorithms

/-! The primitive raw-plan candidate score equals the packing incidence counter. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.Subexp

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def incidenceScorerContext (alphabet : List (Word r Q)) (indices : List (V ⊕ E))
    (default : Word r Q) (fixed : List (Word r Q)) : PairScoreProgram.Context where
  current := (ReadPlan.currentArray default indices.length fixed).map ReadPlan.encodeWord
  width := List.replicate (ReadPlan.wordWidth r Q) true
  alphabet := alphabet.map ReadPlan.encodeWord
  depth := List.replicate 4 true

def incidenceScorerPlan (indices : List (V ⊕ E)) (remaining : List ℕ)
    (pair : I × I) : PairScoreProgram.PlanPair :=
  let activeIndices := active (numberedScoreSupport (Q := Q) ivar factor indices (.inl pair)) remaining
  (incidenceSelectedPlan ivar factor indices indices.length activeIndices pair.1,
   incidenceSelectedPlan ivar factor indices indices.length activeIndices pair.2)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceScorer_pairCount (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default : Word r Q)
    (fixed : List (Word r Q)) (remaining : List ℕ) (hn : remaining.Nodup) (pair : I × I) :
    PairScoreProgram.pairCount (incidenceScorerContext alphabet indices default fixed)
      (incidenceScorerPlan (Q := Q) ivar factor indices remaining pair) =
      scaledCount alphabet (fun η => PackingProgram.incidenceIndicator ivar factor
        (.inl pair) (fun a => η (indexCode indices a)))
        (numberedScoreSupport (Q := Q) ivar factor indices (.inl pair)) 4 remaining
        (decode default fixed) := by
  simpa only [incidenceScorerContext, incidenceScorerPlan, PairScoreProgram.pairCount,
    PairScoreProgram.pairStream, generatedIncidenceLeaves, List.length_replicate,
    ReadPlan.currentArray_length, CollisionTupleProgram.tupleBytes] using
      generatedIncidencePair_count ivar factor alphabet indices hi default fixed
        remaining hn pair.1 pair.2

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceScorer_score (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default : Word r Q)
    (fixed : List (Word r Q)) (remaining : List ℕ) (hn : remaining.Nodup) :
    PairScoreProgram.score (incidenceScorerContext alphabet indices default fixed)
      (pairs.map (incidenceScorerPlan (Q := Q) ivar factor indices remaining)) =
      (PackingProgram.unweightedCounts ivar factor alphabet (pairs.map Sum.inl)
        indices remaining (decode default fixed)).1 := by
  rw [PairScoreProgram.score_eq_sum, List.map_map]
  simp only [Function.comp_def, incidenceScorer_pairCount ivar factor alphabet indices hi
    default fixed remaining hn]
  simp only [PackingProgram.unweightedCounts, commonNumerator, List.map_map, Function.comp_def]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceScorerPlan_eq_selected (indices : List (V ⊕ E))
    (processed n : ℕ) (hsize : n + 1 + processed = indices.length) (pair : I × I) :
    PairPreparationProgram.selectedPair indices.length processed
      (PackingIncidenceProgram.incidencePair ivar factor indices pair) =
      incidenceScorerPlan (Q := Q) ivar factor indices (List.range' (processed + 1) n) pair := by
  rw [PackingIncidenceProgram.selectedPair_eq (Q := Q) ivar factor indices processed n hsize pair]
  rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem candidate_incidenceScore (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default candidate : Word r Q)
    (fixed : List (Word r Q)) (n : ℕ) (width index : List Bool)
    (hsize : n + 1 + fixed.length = indices.length)
    (hw : width.length = ReadPlan.wordWidth r Q) :
    CandidateScoreProgram.candidateScore
      (CandidateScoreRefinement.candidateContext (Δ := 1) alphabet default fixed n width index
        (PairPreparationProgram.selectedPairs indices.length fixed.length
          (pairs.map (PackingIncidenceProgram.incidencePair ivar factor indices))))
      (ReadPlan.encodeWord candidate) =
      (PackingProgram.unweightedCounts ivar factor alphabet (pairs.map Sum.inl)
        indices (List.range' (fixed.length + 1) n) (decode default (candidate :: fixed))).1 := by
  have hp : PairPreparationProgram.selectedPairs indices.length fixed.length
      (pairs.map (PackingIncidenceProgram.incidencePair ivar factor indices)) =
      pairs.map (incidenceScorerPlan (Q := Q) ivar factor indices
        (List.range' (fixed.length + 1) n)) := by
    simp only [PairPreparationProgram.selectedPairs, List.map_map, Function.comp_def,
      incidenceScorerPlan_eq_selected (Q := Q) ivar factor indices fixed.length n hsize]
  unfold CandidateScoreProgram.candidateScore
  rw [hp]
  rw [CandidateScoreRefinement.score_context_congr _
    (incidenceScorerContext alphabet indices default (candidate :: fixed))]
  · exact incidenceScorer_score ivar factor alphabet pairs indices hi default
      (candidate :: fixed) _ List.nodup_range'
  · change fixed.reverse.map ReadPlan.encodeWord ++ ReadPlan.encodeWord candidate ::
      (List.replicate n default).map ReadPlan.encodeWord = _
    change _ = (ReadPlan.currentArray default indices.length (candidate :: fixed)).map ReadPlan.encodeWord
    rw [CandidateScoreRefinement.currentArray_after_candidate default candidate indices.length
      fixed (by omega)]
    have hn : indices.length - (fixed.length + 1) = n := by omega
    simp only [hn, List.map_append, List.map_cons]
  · simpa only [CandidateScoreProgram.pairContext, CandidateScoreRefinement.candidateContext,
      incidenceScorerContext, List.length_replicate] using hw
  · rfl
  · rfl

end Scores
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
