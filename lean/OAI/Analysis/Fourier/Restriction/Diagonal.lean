import OAI.Analysis.Fourier.Restriction.MixedRange
import OAI.MeasureTheory.Kakeya.Overlap

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem exists_strict_diagonal_exponent {c q b : ℝ}
    (hq : 0 < q) (hcb : c < b) (hline : (c - 1) * q < b) :
    ∃ s : ℝ, c < s ∧ s < b ∧ q * (s - 1) < b := by
  have hc : c < min b (1 + b / q) := by
    apply lt_min hcb
    have H := (lt_div_iff₀ hq).mpr hline
    linarith
  obtain ⟨s, hcs, hs⟩ := exists_between hc
  refine ⟨s, hcs, hs.trans_le (min_le_left _ _), ?_⟩
  have H : s - 1 < b / q := by
    have H' := hs.trans_le (min_le_right _ _)
    linarith
  simpa only [mul_comm] using (lt_div_iff₀ hq).mp H

theorem criticalExponent_sub_one {n : ℕ} (hn : 2 ≤ n) :
    OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n - 1 = ((n : ℝ) + 1) / ((n : ℝ) - 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : (n : ℝ) - 1 ≠ 0 := by linarith
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  field_simp
  ring

/-- Diagonal extension estimates arbitrarily close to the critical exponent
give every conjectured strict mixed spherical restriction estimate. -/
theorem sphericalRestriction_of_diagonal
    (hdiag : ∀ n : ℕ, 2 ≤ n → ∀ s : ℝ, OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < s →
      ∃ C : ℝ, 0 < C ∧ ∀ g : Space n → ℂ,
        MemLp g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
        eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal s) volume ≤
          ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture := by
  intro n hn a ha b hb hab
  obtain ⟨s, hs, hsb, has⟩ := exists_strict_diagonal_exponent
    (conjugateExponent_pos ha) hb (by rwa [criticalExponent_sub_one hn])
  have hs1 : 1 < s := by
    have H := (OAI.MeasureTheory.Kakeya.criticalExponent_gt_two hn).trans hs
    linarith
  obtain ⟨C, hC, hCs⟩ := hdiag n hn s hs
  obtain ⟨B, hBt, hB⟩ := sphericalExtension_mixed_diagonal ha hs1 hsb has
    ENNReal.ofReal_ne_top hCs
  refine ⟨B.toReal + 1, by positivity, ?_⟩
  intro g hg
  have H := hB g hg
  have hbound : B ≤ ENNReal.ofReal (B.toReal + 1) := by
    rw [← ENNReal.ofReal_toReal hBt]
    exact ENNReal.ofReal_le_ofReal (by simp)
  constructor
  · exact H.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hBt) hg)
  · exact H.trans (by gcongr)

end OAI.Analysis.Fourier.Restriction
