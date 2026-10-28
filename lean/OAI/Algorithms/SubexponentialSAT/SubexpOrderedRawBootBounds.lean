import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawSparsifyRuntime
import OAI.Algorithms.SubexponentialSAT.SubexpOverhead

namespace OAI.Algorithms

/-!
# Measured bounds for the actual ordered-input boot and its records

The same `Run` supplies frontend, setup, and sparsifier traces. No new
execution or leaf list is chosen to justify a numerical estimate. The
per-record bound uses the actual output's normalization and width facts.
-/

namespace SubexponentialSAT.SubexpOrderedRawBootBounds

open Filter SubexpMainProgram SubexpSetupProgram SubexpComputation

variable {cfg : Config} {er n : ℕ} {hr : 32 ≤ workRegs er} {F : SubexpOrderedRawPrefix.Formula n}

def totalSteps (run : SubexpOrderedRawBoot.Run cfg hr F) : ℕ :=
  run.prefixSteps + run.setupSteps + run.sparsifySteps

def payloadBits (cfg : Config) (L : ℕ) : ℕ :=
  (8 * cfg.k + 5) * (L + 1) ^ (2 * cfg.k + 1)

/-- The bytes read by the actual record iterator are bounded in terms of
the original input, including the variable header. -/
theorem record_length (run : SubexpOrderedRawBoot.Run cfg hr F)
    (bits : List Bool) (hb : bits ∈ run.records) :
    bits.length ≤ payloadBits cfg (SubexpOrderedRawPrefix.bitLength F) := by
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hb
  have hc := run.outcome.correct.clause_nodup G hG
  have hl := run.outcome.correct.literal_nodup G hG
  have hw := run.outcome.correct.width G hG
  have hrw : ExecSunflowerSearch.RawWidthAtMost cfg.k G := by
    intro C hC
    have hwidth := hw (ExecCNF.clauseSet C) (ExecCNF.mem_formulaSet.mpr ⟨C, hC, rfl⟩)
    simpa only [ExecCNF.clauseSet, List.toFinset_card_of_nodup (hl C hC)] using hwidth
  change (Encoding.encodeList (Encoding.encodeList id)
    (ExecSparsifyEncoding.words G)).length ≤ _
  rw [ExecSparsifyEncoding.words_encodeRawFormula]
  exact (ExecQuantitativeSparsify.encodeRawFormula_polynomial G cfg.k hc hrw).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (SubexpOrderedRawPrefix.numVariables_le_bitLength F) 1) _))

private theorem envelope_mono_degree {C a : ℝ} (hC : 0 ≤ C)
    {d e : ℕ} (hde : d ≤ e) (L n : ℕ) :
    runtimeBound C a d L n ≤ runtimeBound C a e L n := by
  have hb : (1 : ℝ) ≤ (L : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb hde) hC) (by positivity)

/-- Actual startup time and actual retained setup words share fixed
input-independent constants. The exponential factor is charged only to time. -/
theorem eventually_bounded (cfg : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
      ∀ᶠ n : ℕ in atTop, ∀ F : SubexpOrderedRawPrefix.Formula n, ExecSunflowerSearch.RawWidthAtMost cfg.k F →
        ∃ run : SubexpOrderedRawBoot.Run cfg hr F,
          (totalSteps run : ℝ) ≤ runtimeBound (C : ℝ) 3 d (SubexpOrderedRawPrefix.bitLength F) n ∧
          SubexpSetupStorage.WordBound (C * (SubexpOrderedRawPrefix.bitLength F + 1) ^ d)
            run.afterSetup := by
  obtain ⟨Cs, ds, hCs, hds, hs⟩ := SubexpOrderedRawBoot.eventually_run cfg hr
  obtain ⟨Ct, dt, _, ht⟩ := SubexpOrderedRawSparsifyRuntime.sparsifySteps_bound cfg hr
  refine ⟨Cs + Ct, ds + dt, by omega, by omega, ?_⟩
  filter_upwards [hs, ht] with n hs ht
  intro F hF
  obtain ⟨run, hsetup, hwords⟩ := hs F hF
  let L := SubexpOrderedRawPrefix.bitLength F
  have he : (1 : ℝ) ≤ (2 : ℝ) ^ (3 * scale n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (by norm_num) (scale_nonneg n))
  have hs0 : ((run.prefixSteps + run.setupSteps : ℕ) : ℝ) ≤
      runtimeBound (Cs : ℝ) 3 ds L n := by
    have hcast : ((run.prefixSteps + run.setupSteps : ℕ) : ℝ) ≤
        (Cs : ℝ) * ((L : ℝ) + 1) ^ ds := by exact_mod_cast hsetup
    exact hcast.trans (le_mul_of_one_le_right (by positivity) he)
  have hs1 := hs0.trans (envelope_mono_degree (Nat.cast_nonneg Cs)
    (show ds ≤ ds + dt by omega) L n)
  have ht1 := (ht F hF run).trans (envelope_mono_degree (Nat.cast_nonneg Ct)
    (show dt ≤ ds + dt by omega) L n)
  have htime : (totalSteps run : ℝ) ≤ runtimeBound ((Cs + Ct : ℕ) : ℝ) 3
      (ds + dt) L n := by
    calc
      _ ≤ runtimeBound (Cs : ℝ) 3 (ds + dt) L n +
          runtimeBound (Ct : ℝ) 3 (ds + dt) L n := by
        simpa only [totalSteps, Nat.cast_add] using add_le_add hs1 ht1
      _ = _ := by unfold runtimeBound; push_cast; ring
  have hwordBound : Cs * (L + 1) ^ ds ≤ (Cs + Ct) * (L + 1) ^ (ds + dt) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  exact ⟨run, htime, SubexpSetupBoundSpec.wordBound_mono hwords hwordBound⟩

/-- Cardinality concerns the exact list consumed by Main, not a separate
existential sparsification. -/
theorem records_bound (cfg : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∃ C d : ℕ, 0 < C ∧ ∀ n : ℕ, SubexpPackingParameters.GoodInput n →
      ∀ F : SubexpOrderedRawPrefix.Formula n, ExecSunflowerSearch.RawWidthAtMost cfg.k F →
      ∀ run : SubexpOrderedRawBoot.Run cfg hr F,
        (run.records.length : ℝ) ≤ runtimeBound (C : ℝ) 2 d (SubexpOrderedRawPrefix.bitLength F) n := by
  obtain ⟨C, d, hC, h⟩ := SubexpOrderedRawSparsifyRuntime.leaves_bound cfg hr
  refine ⟨C, d, hC, ?_⟩
  intro n hn F hF run
  simpa only [SubexpOrderedRawBoot.Run.records, List.length_map] using h n hn F hF run

end SubexponentialSAT.SubexpOrderedRawBootBounds

end OAI.Algorithms
