import OAI.MeasureTheory.Kakeya.Log.RestrictionShift
import OAI.MeasureTheory.Kakeya.Log.RestrictionExtraction

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- Quantitative restriction from a family of thin-shell convolution
kernels. The window and asymptotic constants are uniform in the shell scale;
the logarithmic degree in the multiplier estimate is preserved exactly. -/
theorem logarithmic_local_restriction_of_windowed_kernels {n k : ℕ} (hn : 2 ≤ n)
    (K : ℝ → Space n → ℂ) (w : ℝ → ℝ → ℝ)
    {A B C W J c L : ℝ} (hC : 0 ≤ C) (hW : 0 ≤ W) (hJ : 0 ≤ J)
    (hc : 0 < c) (hL : 0 ≤ L) (hAB : 0 < A ^ 2 + B ^ 2)
    (hKm : ∀ T, 2 ≤ T → Measurable (K T))
    (hKb : ∀ T, 2 ≤ T → ∃ M, ∀ x, ‖K T x‖ ≤ M)
    (hwb : ∀ T, 2 ≤ T → ∀ r, |w T r| ≤ W)
    (hwl : ∀ T, 2 ≤ T → ∀ r t, |w T r - w T t| ≤ J * |r - t| / T)
    (hwpos : ∀ T, 2 ≤ T → ∀ t ∈ Icc T (3 * T), c ≤ w T t)
    (hKas : ∀ T, 2 ≤ T → ∀ x : Space n, 1 ≤ ‖x‖ →
      ‖((T * ‖x‖ ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * K T x -
        (w T ‖x‖ : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B ‖x‖ : ℝ)‖ ≤ C / ‖x‖)
    (hKnorm : ∀ T, 2 ≤ T → ∀ f : Space n → ℂ,
      Measurable f → Integrable f →
      MemLp f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume →
      ∀ R : ℝ, 0 ≤ R → (∀ y, R < ‖y‖ → f y = 0) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution (K T) f)
        (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume ≤
        ENNReal.ofReal (L * (1 + Real.log T) ^ k) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f →
      MemLp f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume →
      (∀ y, R < ‖y‖ → f y = 0) →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        D * ENNReal.ofReal ((1 + Real.log R) ^ k) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume := by
  let β : ℝ := ((n : ℝ) - 1) / 2
  have hβ : 0 ≤ β := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    dsimp [β]
    linarith
  have hp : 1 < OAI.Analysis.Fourier.Restriction.restrictionInputExponent n := (OAI.Analysis.Fourier.Restriction.restrictionInputExponent_bounds hn).1
  have hid : β + 1 - (n : ℝ) / OAI.Analysis.Fourier.Restriction.restrictionInputExponent n = 0 := by
    rw [OAI.Analysis.Fourier.Restriction.div_restrictionInputExponent hn]
    dsimp [β]
    ring
  obtain ⟨D, hD, HD⟩ := windowed_farField_kernel_expansion (n := n) β A B C W J hC hW hJ
  have hco : 0 < c * ‖(A : ℂ) - Complex.I * (B : ℂ)‖ :=
    mul_pos hc (norm_pos_iff.mpr (OAI.Analysis.Fourier.Restriction.outgoing_coefficient_ne_zero hAB))
  apply logarithmic_local_restriction_of_farField hn hco
    (show 0 ≤ 2 * D by positivity) (show 0 ≤ (2 * 3 ^ (β + 1)) * L by positivity)
  intro R hR f hfm hfi hfp hfs T hT hRT hpi
  have hT0 : 0 < T := by linarith
  obtain ⟨M, hM⟩ := hKb T hT
  have herror : ∀ (ω : Space n), ‖ω‖ = 1 → ∀ t ∈ Icc T (3 * T),
      ∀ y, ‖y‖ ≤ R →
      ‖((T * t ^ β : ℝ) : ℂ) * K T (t • ω - y) -
        (w T t : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B (t - inner ℝ ω y) : ℝ)‖ ≤
        D * (1 + R ^ 2) / T := by
    intro ω hω t ht y hy
    have hy' : ‖y‖ ≤ t / 2 := by linarith [ht.1]
    have H := HD T hT0 (K T) (w T) (hwb T hT) (hwl T hT) (hKas T hT)
      ω y t hω (hT.trans ht.1) ht.1 hy'
    have hsq : ‖y‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hy
    exact H.trans (by gcongr)
  have HF := windowed_twoRadius_fourier_norm_bound (show 1 ≤ n by omega)
    (hKm T hT) hM hfm hfi hT0 hβ hc.le
    (show 0 ≤ D * (1 + R ^ 2) / T by positivity) hp.le A B (w T) hfs
    (hwpos T hT) herror hpi
  rw [hid, Real.rpow_zero, mul_one] at HF
  have herr : (2 * (D * (1 + R ^ 2) / T)) * ∫ y, ‖f y‖ =
      (2 * D) * (1 + R ^ 2) / T * ∫ y, ‖f y‖ := by ring
  rw [herr] at HF
  apply HF.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ ENNReal.ofReal (2 * 3 ^ (β + 1)) *
        (ENNReal.ofReal (L * (1 + Real.log T) ^ k) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume) :=
      mul_le_mul' le_rfl (hKnorm T hT f hfm hfi hfp R hR hfs)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end OAI.MeasureTheory.Kakeya
