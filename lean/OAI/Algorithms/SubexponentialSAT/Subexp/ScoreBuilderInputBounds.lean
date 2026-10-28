import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRefinement
import OAI.Algorithms.SubexponentialSAT.ScoreBuilderSizeBounds

namespace OAI.Algorithms

/-! Literal input-size bounds for every reachable candidate-scoring step. -/

namespace SubexponentialSAT.Subexp.ScoreBuilderInputBounds

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

def inputBound (M D q w Δ : ℕ) : ℕ := 16 * (M + D + q + w + Δ + 1) ^ 2

def stepBound (M D q w Δ : ℕ) : ℕ :=
  ScoreBuilderBounds.runtimeBound (inputBound M D q w Δ) q (2 * (Δ + 1))

theorem encodedWords_length {r Q : ℕ} (words : List (Word r Q)) :
    (words.map ReadPlan.encodeWord).flatten.length = words.length * ReadPlan.wordWidth r Q := by
  induction words with
  | nil => simp
  | cons word words ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      ReadPlan.encodeWord_length, List.length_cons, ih]
    ring

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

omit [Fintype V] in
theorem raw_pair_bytes_le (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) (pair : V × V) :
    (PairScoreProgram.pairBytes
      (CandidateScoreRefinement.rawPairPlans P slots vertices factors pair)).length ≤
      8 * ((AssignmentEnumeration.seedIndices vertices factors Δ).length + 1) * (Δ + 1) + 6 := by
  let M := (AssignmentEnumeration.seedIndices vertices factors Δ).length
  have hp (v : V) : (CollisionStreamProgram.planBytes
      (ReadPlan.vertexPlan P slots vertices factors v)).length ≤
      1 + (2 * M + 2) * (Δ + 1) := by
    have h := PairPreparationBounds.planBytes_le (ReadPlan.vertexPlan P slots vertices factors v) M
      (fun n hn => Nat.le_of_lt (ReadPlan.vertexPlan_valid P slots vertices factors hv he v n hn))
    simpa only [ReadPlan.vertexPlan_length] using h
  have hl := hp pair.1
  have hr := hp pair.2
  simp only [CandidateScoreRefinement.rawPairPlans, PairScoreProgram.pairBytes,
    List.length_append, Encoding.length_frame]
  dsimp only [M] at hl hr
  nlinarith only [hl, hr]

omit [Fintype V] [NeZero r] in
theorem original_length (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (fixed : List (Word r Q))
    (n : ℕ) (pairs : List (V × V)) (d : ScoreBuilderProgram.Data)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    (CandidateScoreProgram.original
      (ScoreBuilderInput.context P slots (a :: tail) vertices factors a fixed n pairs d)).length =
      (AssignmentEnumeration.seedIndices vertices factors Δ).length * ReadPlan.wordWidth r Q := by
  change ((fixed.reverse.map ReadPlan.encodeWord).flatten ++
    (ReadPlan.encodeWord a ++ ((List.replicate n a).map ReadPlan.encodeWord).flatten)).length = _
  rw [List.length_append, List.length_append, encodedWords_length, encodedWords_length,
    List.length_reverse, List.length_replicate, ReadPlan.encodeWord_length, ← hsize]
  ring

omit [Fintype V] [NeZero r] in
theorem boundedInputs_of_memory (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (pairs : List (V × V))
    (hpairs : pairs.Perm (vertices.product vertices)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    ScoreBuilderBounds.BoundedInputs
      (ScoreBuilderInput.preparationContext P slots vertices factors pairs d)
      (ScoreBuilderInput.context P slots (a :: tail) vertices factors a fixed n pairs d)
      (inputBound (AssignmentEnumeration.seedIndices vertices factors Δ).length
        vertices.length (a :: tail).length (ReadPlan.wordWidth r Q) Δ) := by
  let M := (AssignmentEnumeration.seedIndices vertices factors Δ).length
  let s := M + vertices.length + (a :: tail).length + ReadPlan.wordWidth r Q + Δ + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hM : M + 1 ≤ s := by dsimp [s]; omega
  have hD : vertices.length ≤ s := by dsimp [s]; omega
  have hq : (a :: tail).length ≤ s := by dsimp [s]; omega
  have hw : ReadPlan.wordWidth r Q ≤ s := by dsimp [s]; omega
  have hΔ : Δ + 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s ^ 2 := le_self_pow₀ hs (by omega)
  have hprod : (M + 1) * (Δ + 1) ≤ s ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hM hΔ
  have hmw : M * ReadPlan.wordWidth r Q ≤ s ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show M ≤ s by omega) hw
  have hD2 : vertices.length ^ 2 ≤ s ^ 2 := by gcongr
  have hfixed : fixed.length ≤ M := by dsimp [M]; omega
  have hcount : pairs.length = vertices.length ^ 2 := by
    calc
      pairs.length = (vertices.product vertices).length := hpairs.length_eq
      _ = vertices.length * vertices.length := List.length_product vertices vertices
      _ = vertices.length ^ 2 := (pow_two _).symm
  have hwidth : (d.stacks 10).length = ReadPlan.wordWidth r Q := by
    simpa only [ReadPlan.encodeWord_length] using hm.width
  change ScoreBuilderBounds.BoundedInputs _ _ (16 * s ^ 2)
  constructor
  · change M ≤ _
    nlinarith only [hM, hs2]
  · change (d.stacks 19).length ≤ _
    rw [hm.processed]
    nlinarith only [hfixed, hM, hs2]
  · change (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)).length ≤ _
    rw [List.length_map, hcount]
    nlinarith only [hD2]
  · intro pair hpair
    change pair ∈ pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors) at hpair
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hpair
    have hp := raw_pair_bytes_le P slots vertices factors hv he p
    change _ ≤ 8 * (M + 1) * (Δ + 1) + 6 at hp
    nlinarith only [hp, hprod, hs, hs2]
  · rw [original_length P slots a tail vertices factors fixed n pairs d hsize]
    change M * ReadPlan.wordWidth r Q ≤ _
    nlinarith only [hmw]
  · change (fixed.reverse.map ReadPlan.encodeWord).length ≤ _
    simp only [List.length_map, List.length_reverse]
    nlinarith only [hfixed, hM, hs2]
  · change (d.stacks 10).length ≤ _
    rw [hwidth]
    nlinarith only [hw, hs2]
  · change (List.replicate (2 * (Δ + 1)) true).length ≤ _
    rw [List.length_replicate]
    nlinarith only [hΔ, hs2]
  · change ((a :: tail).map ReadPlan.encodeWord).length ≤ _
    rw [List.length_map]
    nlinarith only [hq, hs2]

omit [Fintype V] [NeZero r] in
theorem sourceBudget_le (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (pairs : List (V × V))
    (hpairs : pairs.Perm (vertices.product vertices)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    ScoreBuilderProgram.sourceBudget
      (ScoreBuilderInput.preparationContext P slots vertices factors pairs d)
      (ScoreBuilderInput.context P slots (a :: tail) vertices factors a fixed n pairs d) ≤
      stepBound (AssignmentEnumeration.seedIndices vertices factors Δ).length
        vertices.length (a :: tail).length (ReadPlan.wordWidth r Q) Δ := by
  have hc := ScoreBuilderInput.candidate_valid_of_memory P slots a tail vertices factors
    hv he fixed n pairs d hm hsize
  have hb := boundedInputs_of_memory P slots a tail vertices factors hv he fixed n pairs hpairs d hm hsize
  have h := ScoreBuilderBounds.sourceBudget_le _ _ hc _ hb
    (by simp [ScoreBuilderInput.context, CandidateScoreRefinement.candidateContext]) rfl
  simpa only [stepBound, ScoreBuilderInput.context, CandidateScoreRefinement.candidateContext,
    List.length_map, List.length_replicate] using h

omit [Fintype V] [NeZero r] in
theorem cost_le (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (pairs : List (V × V))
    (hpairs : pairs.Perm (vertices.product vertices)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    ScoreBuilderRefinement.cost P slots a tail vertices factors pairs fixed n d ≤
      stepBound (AssignmentEnumeration.seedIndices vertices factors Δ).length
        vertices.length (a :: tail).length (ReadPlan.wordWidth r Q) Δ :=
  sourceBudget_le P slots a tail vertices factors hv he fixed n pairs hpairs d hm hsize

omit [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] in
theorem stepBound_le_polynomial (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (factors : List E) :
    stepBound (AssignmentEnumeration.seedIndices vertices factors Δ).length
      vertices.length (a :: tail).length (ReadPlan.wordWidth r Q) Δ ≤
      (10000 * 31 ^ 6 * 1025 ^ 12) *
        ScoreBuilderSizeBounds.sourceSize vertices.length factors.length
          (blockSize r Q Δ) Q r Δ ^ 50 := by
  have hq : (a :: tail).length = r ^ Q := by
    rw [AssignmentEnumeration.enumeration_length (a :: tail) haNodup haFull, card_word]
  rw [hq, AssignmentEnumeration.seedIndices_length]
  simpa only [stepBound, inputBound, ScoreBuilderBounds.runtimeBound, ReadPlan.wordWidth] using
    ScoreBuilderSizeBounds.runtime_expression_le vertices.length factors.length
      (blockSize r Q Δ) Q r Δ (Nat.pos_of_neZero r) rfl

omit [Fintype V] in
theorem cost_le_polynomial (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (fixed : List (Word r Q)) (n : ℕ) (pairs : List (V × V))
    (hpairs : pairs.Perm (vertices.product vertices)) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length) :
    ScoreBuilderRefinement.cost P slots a tail vertices factors pairs fixed n d ≤
      (10000 * 31 ^ 6 * 1025 ^ 12) *
        ScoreBuilderSizeBounds.sourceSize vertices.length factors.length
          (blockSize r Q Δ) Q r Δ ^ 50 :=
  (cost_le P slots a tail vertices factors hv he fixed n pairs hpairs d hm hsize).trans
    (stepBound_le_polynomial a tail haNodup haFull vertices factors)

omit [Fintype V] [NeZero r] in
/-- The actual builder satisfies the controller contract for arbitrary raw
counter and width bytes having the required lengths. -/
theorem refines (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices)) :
    SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
      (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) a)
      ScoreBuilderProgram.command
      (stepBound (AssignmentEnumeration.seedIndices vertices factors Δ).length
        vertices.length (a :: tail).length (ReadPlan.wordWidth r Q) Δ)
      (AssignmentEnumeration.seedIndices vertices factors Δ).length
      (ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs) := by
  apply ScoreBuilderRefinement.refines_of_cost_bound P slots a tail
    vertices factors hv he pairs hpairs
  intro n fixed d hsize hm _
  exact cost_le P slots a tail vertices factors hv he fixed n pairs hpairs d hm hsize

omit [Fintype V] [NeZero r] in
/-- The fixed assignment program with its scoring-cost premise discharged. -/
theorem assignment_run_bounded (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices)) :
    let indices := AssignmentEnumeration.seedIndices vertices factors Δ
    let env := ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs
    let B := stepBound indices.length vertices.length (a :: tail).length (ReadPlan.wordWidth r Q) Δ
    ∃ e : SequentialProgram.Data,
      BitProgram.RunsIn ScoreBuilderRefinement.assignmentProgram
        (indices.length * (B + SequentialProgram.selectionBudget (a :: tail).length
          (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) indices.length
          (ReadPlan.encodeWord a).length + 3) + 3)
        ((SequentialProgram.initialData ReadPlan.encodeWord a tail indices.length env).withPC
          (some ScoreBuilderRefinement.assignmentProgram.entry)) (e.withPC none) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues P slots a tail vertices indices).reverse.map
        ReadPlan.encodeWord).flatten := by
  apply ScoreBuilderRefinement.assignment_run P slots a tail haNodup haFull
    vertices factors hv he pairs hpairs
  intro n fixed d hsize hm _
  exact cost_le P slots a tail vertices factors hv he fixed n pairs hpairs d hm hsize

end SubexponentialSAT.Subexp.ScoreBuilderInputBounds

end OAI.Algorithms
