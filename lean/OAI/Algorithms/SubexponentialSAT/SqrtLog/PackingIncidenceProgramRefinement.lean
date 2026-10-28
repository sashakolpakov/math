import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCompletionScore

namespace OAI.Algorithms

/-! Exact conditional-incidence numerators produced by the fixed raw scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.Packing

section Refinement
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

def incidenceNumerator (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (n : ℕ)
    (fixed : List (Word r Q)) : ℕ :=
  (PackingProgram.unweightedCounts ivar factor alphabet (pairs.map Sum.inl) indices
    (List.range' fixed.length n) (decode default fixed)).1

theorem candidateScore_raw_perm (alphabet : List (Word r Q)) (a : Word r Q)
    (fixed : List (Word r Q)) (n M : ℕ) (raw other : List PlanPair)
    (d : ScoreBuilderProgram.Data) (candidate : List Bool) (hp : raw.Perm other) :
    CandidateScoreProgram.candidateScore (context alphabet a fixed n M raw d) candidate =
    CandidateScoreProgram.candidateScore (context alphabet a fixed n M other d) candidate := by
  apply CandidateScoreRefinement.score_perm
  exact hp.map (PairPreparationProgram.selectedPair M (d.stacks 19).length)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem scoreBytes_eq (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (n : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hraw : raw.Perm (pairs.map (incidencePair ivar factor indices)))
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n+1) fixed d.stacks)
    (hsize : n+1+fixed.length = indices.length) :
    ScoreBuilderProgram.scoreBytes (context (a::tail) a fixed n indices.length raw d) =
      ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
        UnaryCompare.encode (incidenceNumerator ivar factor (a::tail) pairs indices a
          n (candidate::fixed)))) := by
  unfold ScoreBuilderProgram.scoreBytes CandidateScoreProgram.scoreRecords
  apply congrArg ProgramEncoding.encodeRecords
  change (((a::tail).map ReadPlan.encodeWord).map _) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro candidate _
  apply congrArg UnaryCompare.encode
  rw [candidateScore_raw_perm (a::tail) a fixed n indices.length raw _ d _ hraw]
  have hw : (d.stacks 10).length = ReadPlan.wordWidth r Q := by
    simpa only [ReadPlan.encodeWord_length] using hm.width
  have h := candidate_incidenceScore ivar factor (a::tail) pairs indices hi a candidate
    fixed n (d.stacks 10) (d.stacks 19) hsize hw
  simpa only [context, ScoreBuilderRawInput.context, hm.processed, incidenceNumerator,
    List.length_cons] using h

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem run_from_memory (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (n : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hraw : raw.Perm (pairs.map (incidencePair ivar factor indices)))
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n+1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) d.stacks)
    (hsize : n+1+fixed.length = indices.length) :
    ∃ t ≤ runtimeBound indices.length raw.length (a::tail).length (ReadPlan.wordWidth r Q),
      ∃ e : ScoreBuilderProgram.Data,
      SubexponentialSAT.StructuredCalls.Eval command t d e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
        UnaryCompare.encode (incidenceNumerator ivar factor (a::tail) pairs indices a
          n (candidate::fixed)))) ∧
      (∀ j, j ≠ 0 → e.stacks j = d.stacks j) := by
  have hp : ∀ pair ∈ raw, ValidRawPair indices.length pair := by
    intro pair hpair
    have ht := hraw.mem_iff.mp hpair
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ht
    exact incidencePair_valid ivar factor indices hi p
  obtain ⟨t, ht, regs, he⟩ := command_eval a tail fixed n indices.length raw d hm hh hsize hp
  refine ⟨t, ht, _, he, ?_, ?_⟩
  · simp only [ScoreBuilderProgram.resultState, Function.update_same]
    exact scoreBytes_eq ivar factor a tail fixed pairs indices hi n raw d hraw hm hsize
  · exact output_frame d regs _

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
/-- The concrete producer fits the existing sequential conditional-expectation
controller, and supports the actual generated permutation of all raw pairs. -/
theorem refines (a : Word r Q) (tail : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices) (raw : List PlanPair)
    (hraw : raw.Perm (pairs.map (incidencePair ivar factor indices))) :
    SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
      (incidenceNumerator ivar factor (a::tail) pairs indices a) command
      (runtimeBound indices.length raw.length (a::tail).length (ReadPlan.wordWidth r Q))
      indices.length (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) := by
  intro n fixed d hsize hm _ hh
  obtain ⟨t, ht, e, he, hout, hframe⟩ :=
    run_from_memory ivar factor a tail fixed pairs indices hi n raw d hraw hm hh hsize
  refine ⟨t, ht, e, he, hout, ?_, ?_⟩
  · intro j _ hj
    exact hframe j hj
  · intro j hj
    rw [hframe j (by intro h; subst j; omega)]
    exact hh j hj

end Refinement
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
