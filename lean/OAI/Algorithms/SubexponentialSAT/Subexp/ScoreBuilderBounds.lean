import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram

namespace OAI.Algorithms

/-!
# A uniform bound for the actual complete score builder

The preparation program computes the selected plans. Its proved output-size
bound supplies the pair-payload bound needed by the candidate program.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderBounds

open BitProgram ScoreBuilderProgram

/-- Bounds on literal input lengths and counts, before selected plans are
computed. The prepared-payload bound is derived inside the theorem. -/
structure BoundedInputs (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (B : ℕ) : Prop where
  seedCount : pre.seedCount ≤ B
  processed : pre.processedBits.length ≤ B
  pairCount : pre.pairs.length ≤ B
  pairPayload : ∀ pair ∈ pre.pairs, (PairScoreProgram.pairBytes pair).length ≤ B
  original : (CandidateScoreProgram.original ctx).length ≤ B
  before : ctx.before.length ≤ B
  width : ctx.width.length ≤ B
  depth : ctx.depth.length ≤ B
  candidates : ctx.candidates.length ≤ B

def runtimeBound (B q depth : ℕ) : ℕ := 10000 * 31 ^ 6 * (B + 1) ^ 12 * q ^ depth

theorem sourceBudget_le (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (hc : ctx.Valid) (B : ℕ)
    (h : BoundedInputs pre ctx B) (hA : 1 ≤ ctx.alphabet.length)
    (hlink : ctx.pairs = PairPreparationProgram.selectedPairs
      pre.seedCount pre.processedBits.length pre.pairs) :
    sourceBudget pre ctx ≤ runtimeBound B ctx.alphabet.length ctx.depth.length := by
  let s := B + 1
  let C := 30 * s ^ 2
  let K := ctx.alphabet.length ^ ctx.depth.length
  let T := s ^ 12 * K
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : 1 ≤ K := one_le_pow₀ hA
  have hself : s ≤ s ^ 2 := le_self_pow₀ hs (by omega)
  have hBC : B ≤ C := by
    change B ≤ 30 * (B + 1) ^ 2
    nlinarith
  have hC : C + 1 ≤ 31 * s ^ 2 := by dsimp [C]; nlinarith
  have hpn : ctx.pairs.length ≤ B := by
    rw [hlink]
    simpa only [PairPreparationProgram.selectedPairs, List.length_map] using h.pairCount
  have hpb : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ C := by
    intro pair hpair
    rw [hlink] at hpair
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hpair
    exact PairPreparationBounds.selectedPair_length_le pre raw B h.seedCount (h.pairPayload raw hraw)
  have hcan := CandidateScoreBounds.sourceBudget_le ctx hc C hA
    (h.original.trans hBC) (h.before.trans hBC) (h.width.trans hBC) (h.depth.trans hBC)
    (h.candidates.trans hBC) (hpn.trans hBC) hpb
  have hcan' : CandidateScoreProgram.sourceBudget ctx ≤ (6000 * 31 ^ 6) * T := by
    calc
      _ ≤ 6000 * (31 * s ^ 2) ^ 6 * K := hcan.trans (by gcongr)
      _ = _ := by dsimp [T]; ring
  have hpre := PairPreparationBounds.traceBound_le pre B h.seedCount h.processed h.pairCount h.pairPayload
  have hselected := PairPreparationBounds.selectedPairs_bytes_length_le pre B
    h.seedCount h.pairCount h.pairPayload
  have hscores := CandidateScoreBounds.scoreBytes_length_le ctx B hA h.candidates hpn
  have h5 : s ^ 5 ≤ T := by
    simpa only [T, Nat.mul_one] using Nat.mul_le_mul
      (pow_le_pow_right₀ hs (show 5 ≤ 12 by omega)) hk
  have h3 : s ^ 3 ≤ T := by
    simpa only [T, Nat.mul_one] using Nat.mul_le_mul
      (pow_le_pow_right₀ hs (show 3 ≤ 12 by omega)) hk
  have h2 : s ^ 2 * K ≤ T := Nat.mul_le_mul_right _ (pow_le_pow_right₀ hs (by omega))
  have h1 : 1 ≤ T := Nat.mul_le_mul (one_le_pow₀ hs) hk
  have hp' : PairPreparationProgram.traceBound pre ≤ 30000 * T := hpre.trans (Nat.mul_le_mul_left _ h5)
  have hs' : (preparedBytes pre).length ≤ 63 * T := hselected.trans (Nat.mul_le_mul_left _ h3)
  have ho' : (scoreBytes ctx).length ≤ 5 * T := hscores.trans (by
    change 5 * s ^ 2 * K ≤ 5 * T
    nlinarith only [h2])
  have hsum : sourceBudget pre ctx ≤ (6000 * 31 ^ 6 + 30166) * T := by
    unfold sourceBudget
    nlinarith only [hp', hcan', hs', ho', h1]
  calc
    _ ≤ (6000 * 31 ^ 6 + 30166) * T := hsum
    _ ≤ (10000 * 31 ^ 6) * T := Nat.mul_le_mul_right _ (by norm_num)
    _ = runtimeBound B ctx.alphabet.length ctx.depth.length := by
      simp only [runtimeBound, T, s, K, Nat.mul_assoc]

theorem program_run_bounded (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (hc : ctx.Valid) (B : ℕ)
    (h : BoundedInputs pre ctx B) (hA : 1 ≤ ctx.alphabet.length)
    (hlink : ctx.pairs = PairPreparationProgram.selectedPairs
      pre.seedCount pre.processedBits.length pre.pairs)
    (d : Data) (hi : InputFor pre ctx d) :
    ∃ regs, RunsIn program (runtimeBound B ctx.alphabet.length ctx.depth.length)
      (d.withPC (some program.entry)) ((resultState d regs (scoreBytes ctx)).withPC none) := by
  obtain ⟨regs, n, hn, ht⟩ := program_run pre ctx hc d hi
  exact ⟨regs, n, hn.trans (sourceBudget_le pre ctx hc B h hA hlink), ht⟩

theorem primitive_run_bounded (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (hc : ctx.Valid) (B : ℕ)
    (h : BoundedInputs pre ctx B) (hA : 1 ≤ ctx.alphabet.length)
    (hlink : ctx.pairs = PairPreparationProgram.selectedPairs
      pre.seedCount pre.processedBits.length pre.pairs)
    (d : Data) (hi : InputFor pre ctx d) :
    ∃ regs, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * runtimeBound B ctx.alphabet.length ctx.depth.length)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program ((resultState d regs (scoreBytes ctx)).withPC none)) := by
  obtain ⟨regs, hrun⟩ := program_run_bounded pre ctx hc B h hA hlink d hi
  exact ⟨regs, primitive_execution program hrun⟩

end SubexponentialSAT.Subexp.ScoreBuilderBounds

end OAI.Algorithms
