import OAI.Analysis.Fourier.Restriction.RestrictedBand
import OAI.Analysis.Fourier.Restriction.DyadicAmplitude
import OAI.Analysis.Fourier.Restriction.BandPowers

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def restrictedInterpolationConstant (p r₀ r₁ : ℝ) (C₀ C₁ : ℝ≥0∞) : ℝ≥0∞ :=
  (C₀ * ENNReal.ofReal 2) * ENNReal.ofReal ((1 - (2 : ℝ) ^ (1 + -p / r₀))⁻¹) +
    (C₁ * ENNReal.ofReal ((1 / 2 : ℝ) ^ (-p / r₁))) *
      ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (1 + -p / r₁))⁻¹)

theorem restrictedInterpolationConstant_ne_top {p r₀ r₁ : ℝ} {C₀ C₁ : ℝ≥0∞}
    (hC₀ : C₀ ≠ ⊤) (hC₁ : C₁ ≠ ⊤) :
    restrictedInterpolationConstant p r₀ r₁ C₀ C₁ ≠ ⊤ := by
  unfold restrictedInterpolationConstant
  finiteness

/-- Two neighboring bounded-input restriction estimates yield a strong
estimate on the unit ball of the intermediate input space. -/
theorem restrictedFourierBound_normalized {n : ℕ} {p r₀ r₁ : ℝ}
    (hp : 1 ≤ p) (hr₀ : 0 < r₀) (h₀p : r₀ < p) (hp₁ : p < r₁)
    {C₀ C₁ : ℝ≥0∞}
    (hres₀ : RestrictedFourierBound n r₀ (ENNReal.ofReal p) C₀)
    (hres₁ : RestrictedFourierBound n r₁ (ENNReal.ofReal p) C₁)
    {f : Space n → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (hfn : (∫⁻ x, ‖f x‖ₑ ^ p) ≤ 1) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      restrictedInterpolationConstant p r₀ r₁ C₀ C₁ := by
  have hpp : 0 < p := by linarith
  have hr₁ : 0 < r₁ := hpp.trans hp₁
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  let ρ₀ : ℝ := (2 : ℝ) ^ (1 + -p / r₀)
  let ρ₁ : ℝ := (1 / 2 : ℝ) ^ (1 + -p / r₁)
  have hρ₀ : ρ₀ < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have H : 1 < p / r₀ := (lt_div_iff₀ hr₀).mpr (by simpa using h₀p)
    rw [neg_div]
    linarith
  have hρ₁ : ρ₁ < 1 := by
    apply Real.rpow_lt_one (by norm_num) (by norm_num)
    have H : p / r₁ < 1 := (div_lt_iff₀ hr₁).mpr (by simpa using hp₁)
    rw [neg_div]
    linarith
  have Hhigh (k : ℕ) :
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))))
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (C₀ * ENNReal.ofReal 2) * ENNReal.ofReal (ρ₀ ^ k) := by
    have H := restrictedFourierBound_amplitudeBand hr₀ hpp hres₀ hf hfi hfn
      (l := (2 : ℝ) ^ k) (u := (2 : ℝ) ^ (k + 1)) (by positivity) (by positivity)
    rw [high_band_weight (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_mul (by norm_num)] at H
    simpa only [ρ₀, mul_assoc] using H
  have Hlow (k : ℕ) :
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)))
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (C₁ * ENNReal.ofReal ((1 / 2 : ℝ) ^ (-p / r₁))) * ENNReal.ofReal (ρ₁ ^ k) := by
    have H := restrictedFourierBound_amplitudeBand hr₁ hpp hres₁ hf hfi hfn
      (l := (1 / 2 : ℝ) ^ (k + 1)) (u := (1 / 2 : ℝ) ^ k) (by positivity) (by positivity)
    rw [low_band_weight (by norm_num : (0 : ℝ) < 1 / 2), ENNReal.ofReal_mul (by positivity)] at H
    simpa only [ρ₁, mul_assoc] using H
  apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_tendsto_pointwise (OAI.Analysis.Fourier.Restriction.sphereMeasure n)
    (fun N ↦ (continuous_angularFourier (integrable_amplitudeBand hf hfi _ _)).aestronglyMeasurable)
    (continuous_angularFourier hfi).aestronglyMeasurable
    (tendsto_angularFourier_amplitudeBand hf hfi) hpp
  intro N
  calc
    _ ≤ (∑ k ∈ Finset.range N, eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))))
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) +
      ∑ k ∈ Finset.range N, eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)))
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := eLpNorm_amplitudeBand_dyadic_le hf hfi hq N
    _ ≤ (∑ k ∈ Finset.range N, (C₀ * ENNReal.ofReal 2) * ENNReal.ofReal (ρ₀ ^ k)) +
      ∑ k ∈ Finset.range N, (C₁ * ENNReal.ofReal ((1 / 2 : ℝ) ^ (-p / r₁))) * ENNReal.ofReal (ρ₁ ^ k) :=
      add_le_add (Finset.sum_le_sum (fun k _ ↦ Hhigh k)) (Finset.sum_le_sum (fun k _ ↦ Hlow k))
    _ ≤ _ := add_le_add
      (sum_mul_ofReal_geometric_le _ (by dsimp [ρ₀]; positivity) hρ₀ N)
      (sum_mul_ofReal_geometric_le _ (by dsimp [ρ₁]; positivity) hρ₁ N)

end OAI.Analysis.Fourier.Restriction
