import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateRefinement
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram

namespace OAI.Algorithms

/-!
# Candidate-array and generated-score refinement

The concrete temporary array has the same values as the search decoder after
one candidate is prepended. Generated collision streams may be permuted;
their successful-leaf counts still equal the exact natural evaluator.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreRefinement

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment SubexponentialSAT.SubexpTypeVariance

theorem map_range_getD {A : Type*} (default : A) (M : ℕ) (xs : List A)
    (h : xs.length ≤ M) :
    (List.range M).map (fun i => xs.getD i default) =
      xs ++ List.replicate (M - xs.length) default := by
  induction M generalizing xs with
  | zero =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      simp [hx]
  | succ M ih =>
      cases xs with
      | nil => simp
      | cons x xs =>
          have hh := ih xs (by simpa using h)
          simpa [List.range_succ_eq_map, List.map_map, Function.comp_def] using
            congrArg (List.cons x) hh

theorem currentArray_eq_padding {r Q : ℕ} (default : Word r Q) (M : ℕ)
    (fixed : List (Word r Q)) (h : fixed.length ≤ M) :
    ReadPlan.currentArray default M fixed =
      fixed.reverse ++ List.replicate (M - fixed.length) default := by
  unfold ReadPlan.currentArray
  change (List.range M).map (fun i => SubexponentialSAT.LocalExpectation.decode default fixed i) = _
  simp_rw [AssignmentEnumeration.decode_eq_reverse_getD]
  simpa using map_range_getD default M fixed.reverse (by simpa using h)

theorem currentArray_before_candidate {r Q : ℕ} (default : Word r Q) (M : ℕ)
    (fixed : List (Word r Q)) (h : fixed.length < M) :
    ReadPlan.currentArray default M fixed =
      fixed.reverse ++ default :: List.replicate (M - (fixed.length + 1)) default := by
  rw [currentArray_eq_padding default M fixed (Nat.le_of_lt h)]
  have hn : M - fixed.length = M - (fixed.length + 1) + 1 := by omega
  rw [hn, List.replicate_succ]

theorem currentArray_after_candidate {r Q : ℕ} (default candidate : Word r Q) (M : ℕ)
    (fixed : List (Word r Q)) (h : fixed.length < M) :
    ReadPlan.currentArray default M (candidate :: fixed) =
      fixed.reverse ++ candidate :: List.replicate (M - (fixed.length + 1)) default := by
  rw [currentArray_eq_padding default M (candidate :: fixed) (by simpa using h)]
  simp [List.reverse_cons, List.append_assoc]

/-- The preserving array writer's indexed replacement has exactly the
candidate decoder used by sequentialNumerator. -/
theorem currentArray_set_candidate {r Q : ℕ} (default candidate : Word r Q) (M : ℕ)
    (fixed : List (Word r Q)) (h : fixed.length < M) :
    (ReadPlan.currentArray default M fixed).set fixed.length candidate =
      ReadPlan.currentArray default M (candidate :: fixed) := by
  rw [currentArray_before_candidate default M fixed h,
    currentArray_after_candidate default candidate M fixed h,
    List.set_append_right _ _ (by simp)]
  simp

/-- Direct split-array form for CandidateArrayProgram's temporary copy. -/
theorem encoded_candidate_array {r Q : ℕ} (default candidate : Word r Q) (M : ℕ)
    (fixed : List (Word r Q)) (h : fixed.length < M) :
    (fixed.reverse.map ReadPlan.encodeWord).flatten ++
      (ReadPlan.encodeWord candidate ++
        ((List.replicate (M - (fixed.length + 1)) default).map ReadPlan.encodeWord).flatten) =
      ((ReadPlan.currentArray default M (candidate :: fixed)).map ReadPlan.encodeWord).flatten := by
  rw [currentArray_after_candidate default candidate M fixed h]
  simp [List.map_append, List.flatten_append, List.flatten_cons]

section GeneratedCounts

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

omit [Fintype V] [NeZero r] in
/-- An arbitrary explicit ordering of all vertex pairs yields the same
natural score. Only permutation, not a particular enumeration order, is used. -/
theorem generated_counts_sum (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices)) :
    (pairs.map (fun pair => PaddedCompletion.trueCount
      (CollisionGenerateRefinement.generatedPairLeaves P slots alphabet vertices factors
        default fixed remainingCount pair))).sum =
      NaturalAssignment.sequentialNumerator P slots alphabet vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) default remainingCount fixed := by
  rw [(hpairs.map (fun pair => PaddedCompletion.trueCount
    (CollisionGenerateRefinement.generatedPairLeaves P slots alphabet vertices factors
      default fixed remainingCount pair))).sum_eq]
  simp_rw [CollisionGenerateRefinement.generated_pair_trueCount]
  rw [← PaddedCompletion.trueCount_flatMap]
  exact ReadPlan.plannedNumeratorLeaves_trueCount P slots alphabet vertices factors
    hv he default fixed remainingCount

/-- Exact concrete inputs for the fixed pair scorer. -/
def scorerContext (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) : PairScoreProgram.Context where
  current := (ReadPlan.currentArray default
    (AssignmentEnumeration.seedIndices vertices factors Δ).length fixed).map ReadPlan.encodeWord
  width := List.replicate (ReadPlan.wordWidth r Q) false
  alphabet := alphabet.map ReadPlan.encodeWord
  depth := List.replicate (2 * (Δ + 1)) false

/-- The selected plans consumed by one actual pair-score callback. -/
def selectedPairPlans (vertices : List V) (factors : List E)
    (processed remainingCount : ℕ) (pair : V × V) : PairScoreProgram.PlanPair :=
  let M := (AssignmentEnumeration.seedIndices vertices factors Δ).length
  let remaining := ReadPlan.remainingPlan P slots vertices factors pair processed remainingCount
  (CollisionStreamProgram.completionPlan P slots vertices factors M remaining pair.1,
    CollisionStreamProgram.completionPlan P slots vertices factors M remaining pair.2)

omit [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [NeZero r] in
theorem scorerContext_valid (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (default : Word r Q) (fixed : List (Word r Q)) :
    (scorerContext (Δ := Δ) alphabet vertices factors default fixed).Valid := by
  constructor <;> intro row hrow <;>
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hrow <;>
    simp [scorerContext, ReadPlan.encodeWord_length]

omit [Fintype V] [NeZero r] in
theorem selectedPairPlans_valid (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ) (pair : V × V) :
    PairScoreProgram.ValidPair (scorerContext (Δ := Δ) alphabet vertices factors default fixed)
      (selectedPairPlans P slots vertices factors fixed.length remainingCount pair) := by
  let M := (AssignmentEnumeration.seedIndices vertices factors Δ).length
  let remaining := ReadPlan.remainingPlan P slots vertices factors pair fixed.length remainingCount
  have hr : remaining.length ≤ 2 * (Δ + 1) :=
    ReadPlan.remainingPlan_length_le P slots vertices factors pair fixed.length remainingCount
  have hvalid (v : V) : ∀ i ∈
      CollisionStreamProgram.completionPlan P slots vertices factors M remaining v,
      i < M + 2 * (Δ + 1) := by
    exact ReadPlan.completionPlan_valid M (2 * (Δ + 1)) remaining
      (ReadPlan.vertexPlan P slots vertices factors v) hr
      (ReadPlan.vertexPlan_valid P slots vertices factors hv he v)
  constructor
  · simpa [PairScoreProgram.ValidPair, scorerContext, selectedPairPlans, M, remaining] using hvalid pair.1
  · simpa [PairScoreProgram.ValidPair, scorerContext, selectedPairPlans, M, remaining] using hvalid pair.2

omit [Fintype V] [NeZero r] in
theorem scorer_pairCount (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (default : Word r Q) (fixed : List (Word r Q))
    (remainingCount : ℕ) (pair : V × V) :
    PairScoreProgram.pairCount (scorerContext (Δ := Δ) alphabet vertices factors default fixed)
      (selectedPairPlans P slots vertices factors fixed.length remainingCount pair) =
      PaddedCompletion.trueCount
        (CollisionGenerateRefinement.generatedPairLeaves P slots alphabet vertices factors
          default fixed remainingCount pair) := by
  simp [PairScoreProgram.pairCount, PairScoreProgram.pairStream, scorerContext, selectedPairPlans,
    CollisionGenerateRefinement.generatedPairLeaves, CollisionTupleProgram.tupleBytes]

omit [Fintype V] [NeZero r] in
/-- The actual pair aggregator computes precisely the evaluator used by
chooseMinNat, with no required order beyond a permutation of all ordered pairs. -/
theorem score_eq_sequentialNumerator (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices)) :
    PairScoreProgram.score (scorerContext (Δ := Δ) alphabet vertices factors default fixed)
      (pairs.map (selectedPairPlans P slots vertices factors fixed.length remainingCount)) =
      NaturalAssignment.sequentialNumerator P slots alphabet vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) default remainingCount fixed := by
  rw [PairScoreProgram.score_eq_sum, List.map_map]
  simp only [Function.comp_def, scorer_pairCount]
  exact generated_counts_sum P slots alphabet vertices factors hv he default fixed remainingCount pairs hpairs

omit [Fintype V] [NeZero r] in
theorem candidate_score_eq (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default candidate : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices)) :
    PairScoreProgram.score
      (scorerContext (Δ := Δ) alphabet vertices factors default (candidate :: fixed))
      (pairs.map (selectedPairPlans P slots vertices factors (fixed.length + 1) remainingCount)) =
      NaturalAssignment.sequentialNumerator P slots alphabet vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) default remainingCount (candidate :: fixed) := by
  simpa using score_eq_sequentialNumerator P slots alphabet vertices factors hv he
    default (candidate :: fixed) remainingCount pairs hpairs

omit [Fintype V] [NeZero r] in
/-- Actual halting execution plus the exact natural unary score on port 18. -/
theorem scorer_program_run (alphabet : List (Word r Q)) (vertices : List V)
    (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices)) :
    let ctx := scorerContext (Δ := Δ) alphabet vertices factors default fixed
    let plans := pairs.map (selectedPairPlans P slots vertices factors fixed.length remainingCount)
    BitProgram.RunsIn PairScoreProgram.program (PairScoreProgram.sourceBudget ctx plans)
      ((PairScoreProgram.inputState ctx plans).withPC (some PairScoreProgram.program.entry))
      ((PairScoreProgram.outputState ctx plans).withPC none) ∧
    (PairScoreProgram.outputState ctx plans).stacks 18 = UnaryCompare.encode
      (NaturalAssignment.sequentialNumerator P slots alphabet vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) default remainingCount fixed) := by
  dsimp only
  constructor
  · apply PairScoreProgram.program_run _ _
      (scorerContext_valid alphabet vertices factors default fixed)
    intro pair hp
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp hp
    exact selectedPairPlans_valid P slots alphabet vertices factors hv he default fixed remainingCount original
  · rw [PairScoreProgram.outputState_output,
      score_eq_sequentialNumerator P slots alphabet vertices factors hv he default fixed remainingCount pairs hpairs]


end GeneratedCounts

/-- Depth-two tuple generation on framed vertex plans produces exactly the
pair payload expected by PairScoreProgram, retaining every multiplicity. -/
theorem generated_pair_payloads (plans : List (List ℕ)) :
    (TupleProgram.powerRows
      (plans.map (fun p => Encoding.frame (CollisionStreamProgram.planBytes p))) 2 [[]]).Perm
      ((plans.product plans).map PairScoreProgram.pairBytes) := by
  have h := SubexpTupleRefinement.powerRows_empty_perm
    (plans.map (fun p => Encoding.frame (CollisionStreamProgram.planBytes p))) 2
  apply h.trans
  apply List.Perm.of_eq
  simp [QuarticSearch.vectors, SubexpTupleRefinement.tuplePayload_cons,
    SubexpTupleRefinement.tuplePayload_zero, PairScoreProgram.pairBytes,
    List.product, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
    ← List.map_eq_flatMap]

theorem generated_pair_payloads_decode (plans : List (List ℕ)) :
    ((TupleProgram.powerRows
      (plans.map (fun p => Encoding.frame (CollisionStreamProgram.planBytes p))) 2 [[]]).map
        PairScoreProgram.readPair).Perm (plans.product plans) := by
  have h := (generated_pair_payloads plans).map PairScoreProgram.readPair
  simpa [List.map_map, Function.comp_def] using h

theorem generated_vertex_pair_payloads {V : Type*} (vertices : List V) (plan : V → List ℕ) :
    (TupleProgram.powerRows
      (vertices.map (fun v => Encoding.frame (CollisionStreamProgram.planBytes (plan v)))) 2 [[]]).Perm
      ((vertices.product vertices).map (fun pair => PairScoreProgram.pairBytes (plan pair.1, plan pair.2))) := by
  simpa [List.product, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def] using
    generated_pair_payloads (vertices.map plan)

end SubexponentialSAT.Subexp.CandidateScoreRefinement

end OAI.Algorithms
