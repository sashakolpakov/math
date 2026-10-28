import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawBootBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainCacheBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawInvariant

namespace OAI.Algorithms

/-!
# A bounded initial state for the ordered-input Main leaf loop

One pair of constants is chosen before the input. Its polynomial bounds the
actual setup words and all regenerated persistent caches. The boot time has
the checked subexponential factor; no bound on the pending leaf stream is
inserted into the loop invariant.
-/

namespace SubexponentialSAT.SubexpOrderedRawInitialState

open Filter SubexpComputation SubexpSetupProgram SubexpMainProgram

theorem eventually_run (cfg : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
      ∀ᶠ n : ℕ in atTop, ∀ F : SubexpOrderedRawPrefix.Formula n, ExecSunflowerSearch.RawWidthAtMost cfg.k F →
        ∃ run : SubexpOrderedRawBoot.Run cfg hr F,
          (SubexpOrderedRawBootBounds.totalSteps run : ℝ) ≤
            runtimeBound (C : ℝ) 3 d (SubexpOrderedRawPrefix.bitLength F) n ∧
          SubexpMainInvariant.Invariant cfg run.setupOutput
            (C * (SubexpOrderedRawPrefix.bitLength F + 1) ^ d) run.afterSparsify ∧
          SubexpMainCacheBounds.regeneratedBound (SubexpPackingParameters.p n)
            (SubexpPackingParameters.D n) ≤ C * (SubexpOrderedRawPrefix.bitLength F + 1) ^ d ∧
          SubexpSetupStorage.WordBound (C * (SubexpOrderedRawPrefix.bitLength F + 1) ^ d)
            run.afterSetup := by
  obtain ⟨C, d, hC, hd, hb⟩ := SubexpOrderedRawBootBounds.eventually_bounded cfg hr
  refine ⟨C + 8, d + 2, by omega, by omega, ?_⟩
  filter_upwards [hb, SubexpPackingParameters.eventually_goodInput] with n hb hgood
  intro F hF
  obtain ⟨run, htime, hwords⟩ := hb F hF
  let L := SubexpOrderedRawPrefix.bitLength F
  have hnL := SubexpOrderedRawPrefix.numVariables_le_bitLength F
  have hcommon := SubexpMainCacheBounds.scheduled_cacheBound_le_polynomial
    (initial := C * (L + 1) ^ d) (C := C) (d := d) hgood hnL (le_refl _)
  have hinitial := (SubexpMainCacheBounds.initial_le_cacheBound
    (C * (L + 1) ^ d) (SubexpPackingParameters.p n) (SubexpPackingParameters.D n)).trans hcommon
  have hwords' : SubexpSetupStorage.WordBound ((C + 8) * (L + 1) ^ (d + 2)) run.afterSetup :=
    SubexpSetupBoundSpec.wordBound_mono hwords hinitial
  refine ⟨run, ?_, SubexpOrderedRawInvariant.after_boot run hwords', ?_, hwords'⟩
  · apply htime.trans
    have hbase : (1 : ℝ) ≤ (L : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) L
      linarith
    have hp := pow_le_pow_right₀ hbase (show d ≤ d + 2 by omega)
    have hcoef : (C : ℝ) ≤ ((C + 8 : ℕ) : ℝ) := by exact_mod_cast (show C ≤ C + 8 by omega)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hcoef hp (by positivity) (by positivity)) (by positivity)
  · exact (SubexpMainCacheBounds.regenerated_le_cacheBound
      (C * (L + 1) ^ d) (SubexpPackingParameters.p n) (SubexpPackingParameters.D n)).trans hcommon

end SubexponentialSAT.SubexpOrderedRawInitialState

end OAI.Algorithms
