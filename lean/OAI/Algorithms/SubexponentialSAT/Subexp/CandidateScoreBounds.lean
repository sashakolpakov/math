import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PairRuntimeBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram

namespace OAI.Algorithms

/-! # Polynomial overhead of the actual candidate-scoring loop -/

namespace SubexponentialSAT.Subexp.CandidateScoreBounds

open BitProgram CandidateScoreProgram

theorem updated_length (ctx : Context) (candidate : List Bool)
    (h : candidate.length = ctx.old.length) :
    (updated ctx candidate).length = (original ctx).length := by
  simp only [updated, original, List.length_append, h]

theorem pairContext_flatten_length (ctx : Context) (candidate : List Bool)
    (h : candidate.length = ctx.old.length) :
    (pairContext ctx candidate).current.flatten.length = (original ctx).length := by
  simpa only [pairContext, updated, List.flatten_append, List.flatten_cons] using
    updated_length ctx candidate h

theorem candidateScore_le (ctx : Context) (candidate : List Bool) :
    candidateScore ctx candidate ≤ ctx.pairs.length * ctx.alphabet.length ^ ctx.depth.length :=
  PairScoreProgram.score_le_leafCount (pairContext ctx candidate) ctx.pairs

theorem scoreBytes_length_le (ctx : Context) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length) (hn : ctx.candidates.length ≤ B) (hp : ctx.pairs.length ≤ B) :
    (ProgramEncoding.encodeRecords (scoreRecords ctx)).length ≤
      5 * (B + 1) ^ 2 * ctx.alphabet.length ^ ctx.depth.length := by
  let K := ctx.alphabet.length ^ ctx.depth.length
  have hk : 1 ≤ K := one_le_pow₀ hA
  have hw : ∀ row ∈ scoreRecords ctx, row.length ≤ B * K := by
    intro row hrow
    obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp hrow
    simp only [UnaryCompare.encode, List.length_replicate]
    exact (candidateScore_le ctx candidate).trans (Nat.mul_le_mul_right _ hp)
  have h := PairRuntimeBounds.encoded_length_le (scoreRecords ctx) (B * K) hw
  rw [scoreRecords_length] at h
  calc
    _ ≤ 2 * B * (B * K) + 2 * B + 1 := h.trans (by gcongr)
    _ ≤ 5 * (B + 1) ^ 2 * K := by nlinarith [Nat.mul_le_mul_left (2 * B + 1) hk]

theorem callbackCost_le (ctx : Context) (hc : ctx.Valid) (candidate : List Bool)
    (hcan : candidate ∈ ctx.candidates) (B : ℕ) (hA : 1 ≤ ctx.alphabet.length)
    (ho : (original ctx).length ≤ B) (hb : ctx.before.length ≤ B)
    (hw : ctx.width.length ≤ B) (hd : ctx.depth.length ≤ B) (hn : ctx.pairs.length ≤ B)
    (hp : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    callbackCost ctx candidate ≤ 5200 * (B + 1) ^ 5 * ctx.alphabet.length ^ ctx.depth.length := by
  let s := B + 1
  let K := ctx.alphabet.length ^ ctx.depth.length
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : 1 ≤ K := one_le_pow₀ hA
  have hcand := hc.candidate_width candidate hcan
  have heq : candidate.length = ctx.old.length := hcand.trans hc.old_width.symm
  have hu := updated_length ctx candidate heq
  have hflat := pairContext_flatten_length ctx candidate heq
  have hpair := PairRuntimeBounds.sourceBudget_le (pairContext ctx candidate) ctx.pairs B hA
    (fun row hrow => (hc.alphabet_width row hrow).le) (by simpa only [hflat] using ho) hw hd hn hp
  have hscores := candidateScore_le ctx candidate
  have hscore : candidateScore ctx candidate ≤ B * K := hscores.trans (Nat.mul_le_mul_right _ hn)
  have hbytes := PairRuntimeBounds.pairRecords_length_le ctx.pairs B hp
  have hbytes' : (PairScoreProgram.pairRecords ctx.pairs).length ≤ 3 * s ^ 2 := by
    calc
      _ ≤ 2 * B * B + 2 * B + 1 := hbytes.trans (by gcongr)
      _ ≤ 3 * s ^ 2 := by dsimp [s]; nlinarith
  have harray : CandidateArrayProgram.sourceCost (original ctx).length ctx.before.length ctx.width.length ≤
      100 * s ^ 2 := by
    unfold CandidateArrayProgram.sourceCost
    calc
      _ ≤ 7 * B + 7 * B + B * (14 * B + 10) + 20 * B + 32 := by gcongr
      _ ≤ 100 * s ^ 2 := by dsimp [s]; nlinarith
  have h15 : s ≤ s ^ 5 := le_self_pow₀ hs (by omega)
  have h25 : s ^ 2 ≤ s ^ 5 := pow_le_pow_right₀ hs (by omega)
  have hscale : s ^ 2 ≤ s ^ 5 * K := by simpa using Nat.mul_le_mul h25 hk
  have hscale1 : s ≤ s ^ 5 * K := by simpa using Nat.mul_le_mul h15 hk
  have hscore' : candidateScore ctx candidate ≤ s ^ 5 * K := by
    exact hscore.trans (Nat.mul_le_mul_right _ (by dsimp [s] at h15 ⊢; omega))
  change PairScoreProgram.sourceBudget (pairContext ctx candidate) ctx.pairs ≤ 5000 * s ^ 5 * K at hpair
  change callbackCost ctx candidate ≤ 5200 * s ^ 5 * K
  unfold callbackCost
  rw [hu]
  have hcB : candidate.length ≤ B := hcand.le.trans hw
  dsimp [s] at harray hbytes' hscale hscale1 hscore' hpair ⊢
  nlinarith only [harray, hpair, hscore', hbytes', hscale, hscale1, ho, hcB]

/-- The exponent six is fixed; it accounts for traversing candidates and
their encoded score records as well as executing every pair scorer. -/
theorem sourceBudget_le (ctx : Context) (hc : ctx.Valid) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length) (ho : (original ctx).length ≤ B)
    (hb : ctx.before.length ≤ B) (hw : ctx.width.length ≤ B) (hd : ctx.depth.length ≤ B)
    (hn : ctx.candidates.length ≤ B) (hpn : ctx.pairs.length ≤ B)
    (hp : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    sourceBudget ctx ≤ 6000 * (B + 1) ^ 6 * ctx.alphabet.length ^ ctx.depth.length := by
  let s := B + 1
  let K := ctx.alphabet.length ^ ctx.depth.length
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : 1 ≤ K := one_le_pow₀ hA
  have h15 : s ≤ s ^ 5 := le_self_pow₀ hs (by omega)
  have hscale : s ≤ s ^ 5 * K := by simpa using Nat.mul_le_mul h15 hk
  have hbud := PairRuntimeBounds.budget_bounded (callbackCost ctx) ctx.candidates B (5200 * s ^ 5 * K)
    (fun row hrow => (hc.candidate_width row hrow).le.trans hw)
    (fun row hrow => callbackCost_le ctx hc row hrow B hA ho hb hw hd hpn hp)
  have hstep : 6 * B + 5200 * s ^ 5 * K + 7 ≤ 5213 * s ^ 5 * K := by
    dsimp [s] at hscale ⊢
    nlinarith
  have hbud' : RecordPrograms.budget (callbackCost ctx) ctx.candidates ≤ 5213 * s ^ 6 * K := by
    calc
      _ ≤ ctx.candidates.length * (5213 * s ^ 5 * K) := hbud.trans (Nat.mul_le_mul_left _ hstep)
      _ ≤ s * (5213 * s ^ 5 * K) := Nat.mul_le_mul_right _ (by dsimp [s]; omega)
      _ = _ := by ring
  have hinput := PairRuntimeBounds.encoded_length_le ctx.candidates B
    (fun row hrow => (hc.candidate_width row hrow).le.trans hw)
  have hinput' : (ProgramEncoding.encodeRecords ctx.candidates).length ≤ 3 * s ^ 2 := by
    calc
      _ ≤ 2 * B * B + 2 * B + 1 := hinput.trans (by gcongr)
      _ ≤ 3 * s ^ 2 := by dsimp [s]; nlinarith
  have hout := scoreBytes_length_le ctx B hA hn hpn
  have h26 : s ^ 2 ≤ s ^ 6 := pow_le_pow_right₀ hs (by omega)
  have hscale2 : s ^ 2 ≤ s ^ 6 * K := by simpa using Nat.mul_le_mul h26 hk
  have hout' : (ProgramEncoding.encodeRecords (scoreRecords ctx)).length ≤ 5 * s ^ 6 * K :=
    hout.trans (by gcongr)
  have hone : 1 ≤ s ^ 6 * K := Nat.mul_le_mul (one_le_pow₀ hs) hk
  change 7 * (ProgramEncoding.encodeRecords ctx.candidates).length +
    RecordPrograms.budget (callbackCost ctx) ctx.candidates +
    3 * (ProgramEncoding.encodeRecords (scoreRecords ctx)).length + 14 ≤ 6000 * s ^ 6 * K
  nlinarith only [hbud', hinput', hout', hscale2, hone]

theorem program_run_bounded (ctx : Context) (hc : ctx.Valid) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length) (ho : (original ctx).length ≤ B)
    (hb : ctx.before.length ≤ B) (hw : ctx.width.length ≤ B) (hd : ctx.depth.length ≤ B)
    (hn : ctx.candidates.length ≤ B) (hpn : ctx.pairs.length ≤ B)
    (hp : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B)
    (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn program (6000 * (B + 1) ^ 6 * ctx.alphabet.length ^ ctx.depth.length)
      ((inputState ctx regs).withPC (some program.entry)) ((outputState ctx finalRegs).withPC none) := by
  obtain ⟨finalRegs, n, hn', ht⟩ := program_run ctx hc regs
  exact ⟨finalRegs, n, hn'.trans (sourceBudget_le ctx hc B hA ho hb hw hd hn hpn hp), ht⟩

theorem primitive_run_bounded (ctx : Context) (hc : ctx.Valid) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length) (ho : (original ctx).length ≤ B)
    (hb : ctx.before.length ≤ B) (hw : ctx.width.length ≤ B) (hd : ctx.depth.length ≤ B)
    (hn : ctx.candidates.length ≤ B) (hpn : ctx.pairs.length ≤ B)
    (hp : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B)
    (regs : Fin 16 → Bool) :
    ∃ finalRegs, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (6000 * (B + 1) ^ 6 * ctx.alphabet.length ^ ctx.depth.length))
      (primitiveCfg program ((inputState ctx regs).withPC (some program.entry)))
      (primitiveCfg program ((outputState ctx finalRegs).withPC none)) := by
  obtain ⟨finalRegs, hrun⟩ := program_run_bounded ctx hc B hA ho hb hw hd hn hpn hp regs
  exact ⟨finalRegs, primitive_execution program hrun⟩

def physicalSize (ctx : Context) : ℕ :=
  (original ctx).length + ctx.before.length + ctx.width.length + ctx.depth.length +
    (ProgramEncoding.encodeRecords ctx.candidates).length + (PairScoreProgram.pairRecords ctx.pairs).length

theorem sourceBudget_le_physicalSize (ctx : Context) (hc : ctx.Valid)
    (hA : 1 ≤ ctx.alphabet.length) :
    sourceBudget ctx ≤ 6000 * (physicalSize ctx + 1) ^ 6 * ctx.alphabet.length ^ ctx.depth.length := by
  apply sourceBudget_le ctx hc (physicalSize ctx) hA
  · unfold physicalSize; omega
  · unfold physicalSize; omega
  · unfold physicalSize; omega
  · unfold physicalSize; omega
  · have h := PairRuntimeBounds.length_le_encoded ctx.candidates
    unfold physicalSize; omega
  · have h := PairRuntimeBounds.pair_count_le_encoded ctx.pairs
    unfold physicalSize; omega
  · intro pair hpair
    have h := PairRuntimeBounds.pair_length_le_encoded ctx.pairs pair hpair
    unfold physicalSize; omega

end SubexponentialSAT.Subexp.CandidateScoreBounds

end OAI.Algorithms
