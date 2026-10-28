import OAI.Analysis.Fourier.WavePackets.Periodic
import OAI.Analysis.Fourier.Restriction.Bumps

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem integerVector_dist_ge_one {n : ℕ} {k l : Fin n → ℤ} (hkl : k ≠ l) :
    1 ≤ dist (OAI.Analysis.Fourier.WavePackets.integerVector k) (OAI.Analysis.Fourier.WavePackets.integerVector l) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ l i := by
    by_contra h
    push Not at h
    exact hkl (funext h)
  have hdiff : (1 : ℝ) ≤ |(k i : ℝ) - (l i : ℝ)| := by
    rcases lt_or_gt_of_ne hi with h | h
    · have H : (k i : ℝ) + 1 ≤ l i := by exact_mod_cast (show k i + 1 ≤ l i by omega)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have H : (l i : ℝ) + 1 ≤ k i := by exact_mod_cast (show l i + 1 ≤ k i by omega)
      rw [abs_of_nonneg (by linarith)]
      linarith
  have H := PiLp.norm_apply_le (OAI.Analysis.Fourier.WavePackets.integerVector k - OAI.Analysis.Fourier.WavePackets.integerVector l) i
  change |(k i : ℝ) - (l i : ℝ)| ≤ ‖OAI.Analysis.Fourier.WavePackets.integerVector k - OAI.Analysis.Fourier.WavePackets.integerVector l‖ at H
  exact hdiff.trans (by simpa only [dist_eq_norm] using H)

theorem integerVector_image_separated {n : ℕ} (E : Finset (Fin n → ℤ)) :
    ∀ z ∈ E.image OAI.Analysis.Fourier.WavePackets.integerVector, ∀ w ∈ E.image OAI.Analysis.Fourier.WavePackets.integerVector,
      z ≠ w → 1 ≤ dist z w := by
  classical
  intro z hz w hw hzw
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
  exact integerVector_dist_ge_one (fun h ↦ hzw (congrArg OAI.Analysis.Fourier.WavePackets.integerVector h))

end OAI.Analysis.Fourier.Restriction
