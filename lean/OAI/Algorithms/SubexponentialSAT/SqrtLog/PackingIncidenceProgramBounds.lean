import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram

namespace OAI.Algorithms

/-! Numeric and serialized size bounds for computed incidence scores. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

theorem candidateScore_le {r Q : ℕ} (alphabet : List (Word r Q)) (a : Word r Q)
    (fixed : List (Word r Q)) (n M : ℕ) (raw : List PlanPair)
    (d : ScoreBuilderProgram.Data) (candidate : List Bool) :
    CandidateScoreProgram.candidateScore (context alphabet a fixed n M raw d) candidate ≤
      raw.length * alphabet.length^4 := by
  simpa [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
    PairPreparationProgram.selectedPairs] using
    CandidateScoreBounds.candidateScore_le (context alphabet a fixed n M raw d) candidate

theorem candidateScore_bitSize {r Q : ℕ} (alphabet : List (Word r Q)) (a : Word r Q)
    (fixed : List (Word r Q)) (n M : ℕ) (raw : List PlanPair)
    (d : ScoreBuilderProgram.Data) (candidate : List Bool) :
    (CandidateScoreProgram.candidateScore (context alphabet a fixed n M raw d) candidate).size ≤
      raw.length.size + 4*alphabet.length.size + 1 := by
  apply Nat.size_le.mpr
  have hp : raw.length * alphabet.length^4 ≤
      2^(raw.length.size + 4*alphabet.length.size) := by
    calc
      _ ≤ (2^raw.length.size)*(2^alphabet.length.size)^4 :=
        Nat.mul_le_mul (Nat.lt_size_self _).le (Nat.pow_le_pow_left (Nat.lt_size_self _).le _)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  exact ((candidateScore_le alphabet a fixed n M raw d candidate).trans hp).trans_lt
    (Nat.pow_lt_pow_right (by decide) (by omega))

theorem scoreBytes_length_le {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data) :
    (ScoreBuilderProgram.scoreBytes (context (a::tail) a fixed n M raw d)).length ≤
      5 * (raw.length + (a::tail).length + 1)^2 * (a::tail).length^4 := by
  have h := CandidateScoreBounds.scoreBytes_length_le
    (context (a::tail) a fixed n M raw d) (raw.length + (a::tail).length)
    (by simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext])
    (by simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext])
    (by simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      PairPreparationProgram.selectedPairs])
  simpa [ScoreBuilderProgram.scoreBytes, context, ScoreBuilderRawInput.context,
    CandidateScoreRefinement.candidateContext] using h

/-- The physically written score record is the result of the fixed trace;
every stack besides output zero is restored, including immutable metadata. -/
theorem program_outputs {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState (ScoreBuilderRawInput.environment 1 (a::tail) M raw)
      d.stacks)
    (hsize : n + 1 + fixed.length = M)
    (hp : ∀ pair ∈ raw, ValidRawPair M pair) :
    ∃ e : ScoreBuilderProgram.Data,
      RunsIn program (runtimeBound M raw.length (a::tail).length (ReadPlan.wordWidth r Q)+1)
        (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 0 = ScoreBuilderProgram.scoreBytes (context (a::tail) a fixed n M raw d) ∧
      (e.stacks 0).length ≤ 5*(raw.length+(a::tail).length+1)^2*(a::tail).length^4 ∧
      (∀ j, j ≠ 0 → e.stacks j = d.stacks j) := by
  obtain ⟨regs, hr⟩ := program_runsIn a tail fixed n M raw d hm hh hsize hp
  refine ⟨ScoreBuilderProgram.resultState d regs
    (ScoreBuilderProgram.scoreBytes (context (a::tail) a fixed n M raw d)), hr, ?_, ?_, ?_⟩
  · simp [ScoreBuilderProgram.resultState]
  · simpa [ScoreBuilderProgram.resultState] using scoreBytes_length_le a tail fixed n M raw d
  · exact output_frame d regs _

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
