import OAI.Analysis.Fourier.LocalSmoothing.DyadicReconstruction
import OAI.Analysis.Fourier.LocalSmoothing.DyadicWeights
import OAI.Analysis.Fourier.BesselPotential.Schwartz

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter Set
open scoped ENNReal ContDiff Topology
noncomputable section

namespace OAI.Analysis.PDE.WaveEquation

theorem halfWaveIntegral_zero_schwartz {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    (x : Space n) : OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral 0 f x = f x := by
  simpa only [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral, zero_mul, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul] using OAI.Analysis.Fourier.Restriction.angularInverse_angularFourier_schwartz f x

/-- A spatial multiplier may be reconstructed from summably bounded annular
pieces. The conclusion concerns the actual Schwartz function, not an abstract
extension of the multiplier. -/
theorem schwartz_norm_le_of_dyadic_bounds {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {A : ℝ≥0∞} {w : ℕ → ℝ}
    (hw₀ : ∀ j, 0 ≤ w j) (hw : Summable w)
    {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hlow : eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff 1 0 u) p volume ≤
      ENNReal.ofReal C₀ * A)
    (hann : ∀ j, eLpNorm
      (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j) 0 u)
      p volume ≤ ENNReal.ofReal (C₁ * w j) * A) :
    eLpNorm u p volume ≤ ENNReal.ofReal (C₀ + C₁ * ∑' j, w j) * A := by
  have hc (χ : Space n → ℂ) (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ)
      (h : ℝ) (hh : 0 < h) : AEStronglyMeasurable (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 u) volume :=
    ((OAI.Analysis.Fourier.LocalSmoothing.continuous_frequencyHalfWave_schwartz hχ hs hh u).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hb := OAI.Analysis.Fourier.LocalSmoothing.eLpNorm_le_base_add_tsum_of_tendsto
    (hc _ (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff n) (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingLowCutoff n) 1
      (by norm_num))
    (fun j ↦ hc _ (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingAnnularCutoff n)
      (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingAnnularCutoff n) _ (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j))
    u.continuous.aestronglyMeasurable hp
    (fun x ↦ by simpa only [halfWaveIntegral_zero_schwartz] using
      OAI.Analysis.Fourier.LocalSmoothing.tendsto_smoothing_wave_dyadic_partition 0 u x)
  apply hb.trans
  calc
    _ ≤ ENNReal.ofReal C₀ * A + ∑' j, ENNReal.ofReal (C₁ * w j) * A :=
      add_le_add hlow (ENNReal.tsum_le_tsum hann)
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul hC₁]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
        ← ENNReal.ofReal_tsum_of_nonneg hw₀ hw, ← ENNReal.ofReal_mul hC₁,
        ← add_mul, ← ENNReal.ofReal_add hC₀ (mul_nonneg hC₁ (tsum_nonneg hw₀))]

/-- Exact removal of a scalar factor from an angular-frequency multiplier. -/
theorem frequencyHalfWave_zero_transfer {n : ℕ}
    (f u : SchwartzMap (Space n) ℂ) (χ a : Space n → ℂ) (h c : ℝ)
    (he : ∀ ξ, χ (h • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ =
      (c : ℂ) * a (h • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 u x = c • OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave a h 0 f x := by
  simp only [OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave, zero_mul, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, OAI.Analysis.Fourier.LocalSmoothing.angularInverse]
  simp_rw [he, mul_assoc (c : ℂ)]
  rw [show (fun ξ : Space n ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
      ((c : ℂ) * (a (h • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ))) =
      fun ξ ↦ c • (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
        a (h • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) by
    funext ξ; simp only [Complex.real_smul]; ring]
  rw [integral_smul, smul_comm]
  simp only [mul_assoc]

end OAI.Analysis.PDE.WaveEquation
