import OAI.Analysis.Fourier.Dispersion.Frequency
import OAI.Analysis.Fourier.LocalSmoothing.DyadicSupport
import OAI.Analysis.Fourier.LocalSmoothing.DyadicWeights
import OAI.Analysis.Fourier.BesselPotential.Annular
import OAI.Analysis.Fourier.BesselPotential.AnnularLog

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

theorem frequencyDispersion_annularProject {n : ℕ} (disp : Space n → ℝ) {φ χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (heq : ∀ ξ, φ ξ ≠ 0 → χ ξ = 1) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (t : ℝ) (x : Space n) :
    frequencyDispersion disp φ h t (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f) x =
      frequencyDispersion disp φ h t f x := by
  unfold frequencyDispersion
  congr 1
  funext ξ
  rw [OAI.Analysis.Fourier.BochnerRiesz.angularFourier_annularProject hχ hc hh f]
  by_cases hz : φ (h • ξ) = 0
  · simp only [hz, mul_zero, zero_mul]
  · rw [heq (h • ξ) hz, one_mul]

/-- Sobolev input weights turn an all-p annular bound into a geometrically
summable bound, with exactly the positive loss requested by the source. -/
theorem dispersion_dyadic_sobolev_estimate {n : ℕ} (disp : Space n → ℝ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) (s : ℝ) (A : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hfreq : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦
        frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff h z.2 f z.1) p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (C * h^(-s) * (1+Real.log (1/h))^A) * eLpNorm f p volume)
    (ε : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦
        frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j) z.2 f z.1)
        p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (D * (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j ^ ε * OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicLog j ^ A)) *
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (s+ε) f) p volume := by
  obtain ⟨χ,hχ,hc,hzero,heq,hsmall⟩ := OAI.Analysis.Fourier.LocalSmoothing.exists_smoothing_enlarged_cutoff n
  obtain ⟨B,hB,hb⟩ := OAI.Analysis.Fourier.BesselPotential.annularProject_inverse_bessel_bound hχ hc hzero (s+ε)
  refine ⟨C*B, mul_nonneg hC hB, ?_⟩
  intro j f
  let h := OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j
  have hh : 0 < h := OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j
  have hone : h ≤ 1 := OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_le_one j
  have hL : 0 < 1+Real.log (1/h) := OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicLog_pos j
  have hF := hfreq h hh hone (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f)
  simp only [frequencyDispersion_annularProject disp hχ hc heq hh f] at hF
  have hI := hb h hh hone f p hp hpt
  have hnon : 0 ≤ C * h^(-s) * (1+Real.log (1/h))^A := by positivity
  have hpow : h^(-s) * h^(s+ε) = h^ε := by
    rw [← Real.rpow_add hh]
    congr 1
    ring
  calc
    _ ≤ ENNReal.ofReal (C*h^(-s)*(1+Real.log (1/h))^A) * eLpNorm
        (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f) p volume := hF
    _ ≤ ENNReal.ofReal (C*h^(-s)*(1+Real.log (1/h))^A) *
        (ENNReal.ofReal (B*h^(s+ε)) * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (s+ε) f) p volume) :=
      mul_le_mul' le_rfl hI
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hnon]
      congr 2
      change C*h^(-s)*(1+Real.log (1/h))^A*(B*h^(s+ε)) =
        C*B*(h^ε*(1+Real.log (1/h))^A)
      calc
        _ = C*B*(h^(-s)*h^(s+ε))*(1+Real.log (1/h))^A := by ring
        _ = _ := by rw [hpow]; ring

/-- The logarithmic input weight gives precisely the summable power of
the dyadic logarithm; the derivative orders cancel without any loss. -/
theorem dispersion_dyadic_log_estimate {n : ℕ} (disp : Space n → ℝ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) (s : ℝ) (A : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hfreq : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦
        frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff h z.2 f z.1) p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (C * h^(-s) * (1+Real.log (1/h))^A) * eLpNorm f p volume)
    (B : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦
        frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j) z.2 f z.1)
        p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (D * (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicLog j ^ A * OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicLog j ^ (-B))) *
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) p volume := by
  obtain ⟨χ,hχ,hc,hzero,heq,hsmall⟩ := OAI.Analysis.Fourier.LocalSmoothing.exists_smoothing_enlarged_cutoff n
  have hsmall' : ∀ ξ, ‖ξ‖ ≤ 2 → χ ξ = 0 := fun ξ hξ ↦ hsmall ξ (by linarith)
  obtain ⟨D,hD,hd⟩ :=
    OAI.Analysis.Fourier.BesselPotential.annularProject_inverse_log_bessel_bound_of_vanishing hχ hc hsmall' s B
  refine ⟨C*D, mul_nonneg hC hD, ?_⟩
  intro j f
  let h := OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j
  have hh : 0 < h := OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j
  have hone : h ≤ 1 := OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_le_one j
  have hL : 0 < 1+Real.log (1/h) := OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicLog_pos j
  have hF := hfreq h hh hone (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f)
  simp only [frequencyDispersion_annularProject disp hχ hc heq hh f] at hF
  have hI := hd h hh hone f p hp hpt
  have hnon : 0 ≤ C * h^(-s) * (1+Real.log (1/h))^A := by positivity
  have hpow : h^(-s) * h^s = 1 := by rw [← Real.rpow_add hh, neg_add_cancel, Real.rpow_zero]
  calc
    _ ≤ ENNReal.ofReal (C*h^(-s)*(1+Real.log (1/h))^A) * eLpNorm
        (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f) p volume := hF
    _ ≤ ENNReal.ofReal (C*h^(-s)*(1+Real.log (1/h))^A) *
        (ENNReal.ofReal (D*h^s*(1+Real.log (1/h))^(-B)) *
          eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) p volume) := mul_le_mul' le_rfl hI
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hnon]
      congr 2
      change C*h^(-s)*(1+Real.log (1/h))^A*(D*h^s*(1+Real.log (1/h))^(-B)) =
        C*D*((1+Real.log (1/h))^A*(1+Real.log (1/h))^(-B))
      calc
        _ = C*D*(h^(-s)*h^s)*((1+Real.log (1/h))^A*(1+Real.log (1/h))^(-B)) := by ring
        _ = _ := by rw [hpow, mul_one]

end OAI.Analysis.Fourier.Dispersion
