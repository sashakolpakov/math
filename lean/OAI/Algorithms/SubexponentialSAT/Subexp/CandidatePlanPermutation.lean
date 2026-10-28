import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateContextRefinement

namespace OAI.Algorithms

/-! Generated raw-plan order does not change the candidate scores. -/

namespace SubexponentialSAT.Subexp.CandidateScoreRefinement

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

theorem score_perm (ctx : PairScoreProgram.Context)
    {left right : List PairScoreProgram.PlanPair} (h : left.Perm right) :
    PairScoreProgram.score ctx left = PairScoreProgram.score ctx right := by
  simp only [PairScoreProgram.score_eq_sum]
  exact (h.map (PairScoreProgram.pairCount ctx)).sum_eq

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {Δ : ℕ} (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

omit [Fintype V] in
theorem prepared_pairs_perm (vertices : List V) (factors : List E)
    (processed remainingCount : ℕ) (rawPlans : List PairScoreProgram.PlanPair)
    (pairs : List (V × V))
    (hsize : processed + 1 + remainingCount =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hraw : rawPlans.Perm (pairs.map (rawPairPlans P slots vertices factors))) :
    (PairPreparationProgram.selectedPairs
      (AssignmentEnumeration.seedIndices vertices factors Δ).length processed rawPlans).Perm
      (pairs.map (selectedPairPlans P slots vertices factors (processed + 1) remainingCount)) := by
  have h := hraw.map (PairPreparationProgram.selectedPair
    (AssignmentEnumeration.seedIndices vertices factors Δ).length processed)
  change (PairPreparationProgram.selectedPairs _ _ rawPlans).Perm
    (PairPreparationProgram.selectedPairs _ _ (pairs.map (rawPairPlans P slots vertices factors))) at h
  rw [prepared_pairs_eq P slots vertices factors processed remainingCount pairs hsize] at h
  exact h

variable {r Q : ℕ} [NeZero r]

omit [Fintype V] [NeZero r] in
theorem score_eq_sequentialNumerator_perm (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (plans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hplans : plans.Perm
      (pairs.map (selectedPairPlans P slots vertices factors fixed.length remainingCount)))
    (hpairs : pairs.Perm (vertices.product vertices)) :
    PairScoreProgram.score (scorerContext (Δ := Δ) alphabet vertices factors default fixed) plans =
      NaturalAssignment.sequentialNumerator P slots alphabet vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) default remainingCount fixed := by
  rw [score_perm _ hplans]
  exact score_eq_sequentialNumerator P slots alphabet vertices factors hv he
    default fixed remainingCount pairs hpairs

omit [Fintype V] [NeZero r] in
theorem candidateContext_valid_perm (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (width index : List Bool) (plans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hwidth : width.length = ReadPlan.wordWidth r Q) (hindex : index.length = fixed.length)
    (hsize : remainingCount + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hplans : plans.Perm (pairs.map
      (selectedPairPlans P slots vertices factors (fixed.length + 1) remainingCount))) :
    (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index plans).Valid := by
  have hc := candidateContext_valid P slots alphabet vertices factors hv he default fixed remainingCount
    width index _ pairs hwidth hindex hsize rfl
  refine ⟨hc.index_length, hc.before_width, hc.old_width, hc.after_width,
    hc.alphabet_width, hc.candidate_width, ?_⟩
  intro pair hp
  exact hc.pairs_valid pair (hplans.mem_iff.mp hp)

omit [Fintype V] [NeZero r] in
theorem candidateContext_score_eq_perm (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default candidate : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (width index : List Bool) (plans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hwidth : width.length = ReadPlan.wordWidth r Q)
    (hsize : remainingCount + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hplans : plans.Perm (pairs.map
      (selectedPairPlans P slots vertices factors (fixed.length + 1) remainingCount)))
    (hpairs : pairs.Perm (vertices.product vertices)) :
    CandidateScoreProgram.candidateScore
      (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index plans)
      (ReadPlan.encodeWord candidate) =
      NaturalAssignment.sequentialNumerator P slots alphabet vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) default remainingCount (candidate :: fixed) := by
  change PairScoreProgram.score
    (CandidateScoreProgram.pairContext
      (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index plans)
      (ReadPlan.encodeWord candidate)) plans = _
  rw [score_perm _ hplans]
  exact candidateContext_score_eq P slots alphabet vertices factors hv he default candidate fixed
    remainingCount width index _ pairs hwidth hsize rfl hpairs

omit [Fintype V] [NeZero r] in
theorem candidateContext_scoreRecords_perm (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (width index : List Bool) (plans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hwidth : width.length = ReadPlan.wordWidth r Q)
    (hsize : remainingCount + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hplans : plans.Perm (pairs.map
      (selectedPairPlans P slots vertices factors (fixed.length + 1) remainingCount)))
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
  exact congrArg UnaryCompare.encode (candidateContext_score_eq_perm P slots alphabet vertices factors
    hv he default candidate fixed remainingCount width index plans pairs hwidth hsize hplans hpairs)

omit [Fintype V] [NeZero r] in
theorem candidateContext_scoreRecords_prepared (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (width index : List Bool) (rawPlans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hwidth : width.length = ReadPlan.wordWidth r Q)
    (hsize : remainingCount + 1 + fixed.length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hraw : rawPlans.Perm (pairs.map (rawPairPlans P slots vertices factors)))
    (hpairs : pairs.Perm (vertices.product vertices)) :
    CandidateScoreProgram.scoreRecords
      (candidateContext (Δ := Δ) alphabet default fixed remainingCount width index
        (PairPreparationProgram.selectedPairs
          (AssignmentEnumeration.seedIndices vertices factors Δ).length fixed.length rawPlans)) =
      alphabet.map (fun candidate => UnaryCompare.encode
        (NaturalAssignment.sequentialNumerator P slots alphabet vertices
          (AssignmentEnumeration.seedIndices vertices factors Δ) default remainingCount
          (candidate :: fixed))) := by
  apply candidateContext_scoreRecords_perm P slots alphabet vertices factors hv he default fixed
    remainingCount width index _ pairs hwidth hsize
  · exact prepared_pairs_perm P slots vertices factors fixed.length remainingCount rawPlans pairs
      (by omega) hraw
  · exact hpairs

end SubexponentialSAT.Subexp.CandidateScoreRefinement

end OAI.Algorithms
