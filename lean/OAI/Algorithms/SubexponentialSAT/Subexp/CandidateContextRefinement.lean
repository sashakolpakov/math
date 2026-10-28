import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreRefinement
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram

namespace OAI.Algorithms

/-! Candidate contexts and selected plans refine the natural score evaluator. -/

namespace SubexponentialSAT.Subexp.CandidateScoreRefinement

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment SubexponentialSAT.SubexpTypeVariance

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

def rawPairPlans (vertices : List V) (factors : List E) (pair : V × V) : PairScoreProgram.PlanPair :=
  (ReadPlan.vertexPlan P slots vertices factors pair.1,
    ReadPlan.vertexPlan P slots vertices factors pair.2)

omit [Fintype V] in
theorem prepared_pair_eq (vertices : List V) (factors : List E)
    (processed remainingCount : ℕ) (pair : V × V)
    (hsize : processed + 1 + remainingCount =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    PairPreparationProgram.selectedPair
      (AssignmentEnumeration.seedIndices vertices factors Δ).length processed
      (rawPairPlans P slots vertices factors pair) =
      selectedPairPlans P slots vertices factors (processed + 1) remainingCount pair := by
  let M := (AssignmentEnumeration.seedIndices vertices factors Δ).length
  have hr : PairPreparationProgram.remaining M processed
      (rawPairPlans P slots vertices factors pair) =
      ReadPlan.remainingPlan P slots vertices factors pair (processed + 1) remainingCount := by
    unfold PairPreparationProgram.remaining rawPairPlans
    rw [ActivePlanProgram.active_reverse_left]
    change ActivePlanProgram.active (List.range M)
      (ReadPlan.pairPlan P slots vertices factors pair) (processed + 1) = _
    rw [ActivePlanProgram.active_eq_remainingPlan]
    have hn : M - (processed + 1) = remainingCount := by dsimp [M]; omega
    rw [hn]
  change (ReadPlan.completionPlan M _ _, ReadPlan.completionPlan M _ _) = _
  rw [hr]
  rfl

omit [Fintype V] in
theorem prepared_pairs_eq (vertices : List V) (factors : List E)
    (processed remainingCount : ℕ) (pairs : List (V × V))
    (hsize : processed + 1 + remainingCount =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    PairPreparationProgram.selectedPairs
      (AssignmentEnumeration.seedIndices vertices factors Δ).length processed
      (pairs.map (rawPairPlans P slots vertices factors)) =
      pairs.map (selectedPairPlans P slots vertices factors (processed + 1) remainingCount) := by
  simp only [PairPreparationProgram.selectedPairs, List.map_map, Function.comp_def,
    prepared_pair_eq P slots vertices factors processed remainingCount _ hsize]

/-- Runtime width and processed-index bytes are preserved literally. Only
their lengths enter the semantics. -/
def candidateContext (alphabet : List (Word r Q)) (default : Word r Q)
    (fixed : List (Word r Q)) (remainingCount : ℕ) (width index : List Bool)
    (plans : List PairScoreProgram.PlanPair) : CandidateScoreProgram.Context where
  before := fixed.reverse.map ReadPlan.encodeWord
  old := ReadPlan.encodeWord default
  after := (List.replicate remainingCount default).map ReadPlan.encodeWord
  width := width
  alphabet := alphabet.map ReadPlan.encodeWord
  depth := List.replicate (2 * (Δ + 1)) true
  index := index
  candidates := alphabet.map ReadPlan.encodeWord
  pairs := plans

omit [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [NeZero r] in
theorem candidate_pair_current (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (default candidate : Word r Q) (fixed : List (Word r Q))
    (remainingCount : ℕ) (width index : List Bool) (plans : List PairScoreProgram.PlanPair)
    (hsize : remainingCount + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    (CandidateScoreProgram.pairContext
      (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index plans)
      (ReadPlan.encodeWord candidate)).current =
    (scorerContext (Δ := Δ) alphabet vertices factors default (candidate :: fixed)).current := by
  change fixed.reverse.map ReadPlan.encodeWord ++ ReadPlan.encodeWord candidate ::
    (List.replicate remainingCount default).map ReadPlan.encodeWord = _
  change _ = (ReadPlan.currentArray default
    (AssignmentEnumeration.seedIndices vertices factors Δ).length (candidate :: fixed)).map ReadPlan.encodeWord
  rw [currentArray_after_candidate default candidate _ fixed (by omega)]
  have hn : (AssignmentEnumeration.seedIndices vertices factors Δ).length -
      (fixed.length + 1) = remainingCount := by omega
  rw [hn]
  simp only [List.map_append, List.map_cons]

theorem score_context_congr (a b : PairScoreProgram.Context)
    (hc : a.current = b.current) (hw : a.width.length = b.width.length)
    (ha : a.alphabet = b.alphabet) (hd : a.depth.length = b.depth.length)
    (plans : List PairScoreProgram.PlanPair) :
    PairScoreProgram.score a plans = PairScoreProgram.score b plans := by
  have hcount : PairScoreProgram.pairCount a = PairScoreProgram.pairCount b := by
    funext pair
    simp only [PairScoreProgram.pairCount, PairScoreProgram.pairStream, hc, hw, ha, hd]
  simp only [PairScoreProgram.score_eq_sum, hcount]

omit [Fintype V] [NeZero r] in
theorem candidateContext_valid (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (width index : List Bool) (plans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hwidth : width.length = ReadPlan.wordWidth r Q) (hindex : index.length = fixed.length)
    (hsize : remainingCount + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hplans : plans = pairs.map
      (selectedPairPlans P slots vertices factors (fixed.length + 1) remainingCount)) :
    (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index plans).Valid := by
  constructor
  · simpa [candidateContext] using hindex
  · intro row hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    simp [candidateContext, hwidth, ReadPlan.encodeWord_length]
  · simp [candidateContext, hwidth, ReadPlan.encodeWord_length]
  · intro row hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    simp [candidateContext, hwidth, ReadPlan.encodeWord_length]
  · intro row hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    simp [candidateContext, hwidth, ReadPlan.encodeWord_length]
  · intro row hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    simp [candidateContext, hwidth, ReadPlan.encodeWord_length]
  · intro pair hp
    change pair ∈ plans at hp
    rw [hplans] at hp
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp hp
    have hc := candidate_pair_current alphabet vertices factors default default fixed
      remainingCount width index plans hsize
    have hvp := selectedPairPlans_valid P slots alphabet vertices factors hv he
      default (default :: fixed) remainingCount original
    change PairScoreProgram.ValidPair
      (CandidateScoreProgram.pairContext
        (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index plans)
        (ReadPlan.encodeWord default))
      (selectedPairPlans P slots vertices factors (fixed.length + 1) remainingCount original)
    unfold PairScoreProgram.ValidPair
    rw [hc]
    simpa [PairScoreProgram.ValidPair, CandidateScoreProgram.pairContext,
      candidateContext, scorerContext] using hvp

omit [Fintype V] [NeZero r] in
theorem candidateContext_score_eq (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default candidate : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (width index : List Bool) (plans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hwidth : width.length = ReadPlan.wordWidth r Q)
    (hsize : remainingCount + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hplans : plans = pairs.map
      (selectedPairPlans P slots vertices factors (fixed.length + 1) remainingCount))
    (hpairs : pairs.Perm (vertices.product vertices)) :
    CandidateScoreProgram.candidateScore
      (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index plans)
      (ReadPlan.encodeWord candidate) =
      NaturalAssignment.sequentialNumerator P slots alphabet vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) default remainingCount (candidate :: fixed) := by
  unfold CandidateScoreProgram.candidateScore
  change PairScoreProgram.score
    (CandidateScoreProgram.pairContext
      (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index plans)
      (ReadPlan.encodeWord candidate)) plans = _
  have hc := candidate_pair_current alphabet vertices factors default candidate fixed
    remainingCount width index plans hsize
  rw [score_context_congr _ (scorerContext (Δ := Δ) alphabet vertices factors default (candidate :: fixed))
    hc (by simpa [CandidateScoreProgram.pairContext, candidateContext, scorerContext] using hwidth)
    rfl (by simp [CandidateScoreProgram.pairContext, candidateContext, scorerContext]) plans, hplans]
  exact candidate_score_eq P slots alphabet vertices factors hv he default candidate
    fixed remainingCount pairs hpairs

omit [Fintype V] [NeZero r] in
theorem candidateContext_scoreRecords (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (width index : List Bool) (plans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hwidth : width.length = ReadPlan.wordWidth r Q)
    (hsize : remainingCount + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hplans : plans = pairs.map
      (selectedPairPlans P slots vertices factors (fixed.length + 1) remainingCount))
    (hpairs : pairs.Perm (vertices.product vertices)) :
    CandidateScoreProgram.scoreRecords
      (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index plans) =
      alphabet.map (fun candidate => UnaryCompare.encode
        (NaturalAssignment.sequentialNumerator P slots alphabet vertices
          (AssignmentEnumeration.seedIndices vertices factors Δ) default remainingCount
          (candidate :: fixed))) := by
  change (alphabet.map ReadPlan.encodeWord).map (fun candidate => UnaryCompare.encode
    (CandidateScoreProgram.candidateScore
      (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index plans) candidate)) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro candidate _
  exact congrArg UnaryCompare.encode (candidateContext_score_eq P slots alphabet vertices factors
    hv he default candidate fixed remainingCount width index plans pairs hwidth hsize hplans hpairs)


end SubexponentialSAT.Subexp.CandidateScoreRefinement

end OAI.Algorithms
