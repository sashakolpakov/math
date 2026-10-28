import OAI.Analysis.Fourier.LocalSmoothing.DyadicAssembly
import OAI.Analysis.Fourier.LocalSmoothing.DyadicEstimates

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

/-- The source's positive-loss summation step, retaining the exact Bessel
potential on the right and proving both integrability statements. -/
theorem localSmoothing_sobolev_of_frequency_bounds {n : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) (s : ℝ) (A : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hfreq : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦
        frequencyHalfWave smoothingAnnularCutoff h z.2 f z.1) p (observationMeasure n) ≤
      ENNReal.ofReal (C * h^(-s) * (1+Real.log (1/h))^A) * eLpNorm f p volume)
    {ε : ℝ} (hε : 0 < ε) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hlow : ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ frequencyHalfWave smoothingLowCutoff 1 z.2 f z.1)
        p (observationMeasure n) ≤ ENNReal.ofReal C₀ * eLpNorm (besselPotential (s+ε) f) p volume) :
    ∃ D : ℝ, 0 < D ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (besselPotential (s+ε) f) p volume ∧
      MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) p (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) p (observationMeasure n) ≤
        ENNReal.ofReal D * eLpNorm (besselPotential (s+ε) f) p volume := by
  obtain ⟨C₁,hC₁,hann⟩ := smoothing_dyadic_sobolev_estimate hp hpt s A hC hfreq ε
  let w : ℕ → ℝ := fun j ↦ smoothingDyadicScale j ^ ε * smoothingDyadicLog j ^ A
  have hw₀ (j : ℕ) : 0 ≤ w j := mul_nonneg
    (Real.rpow_nonneg (smoothingDyadicScale_pos j).le _)
    (pow_nonneg (smoothingDyadicLog_pos j).le _)
  have hw : Summable w := summable_smoothing_sobolev_weights A hε
  let D : ℝ := C₀ + C₁ * ∑' j, w j
  have hD : 0 ≤ D := add_nonneg hC₀ (mul_nonneg hC₁ (tsum_nonneg hw₀))
  refine ⟨D+1, by linarith, ?_⟩
  intro f
  have hmem := OAI.Analysis.Fourier.BesselPotential.memLp_besselPotential (s+ε) f p
  obtain ⟨hsol,hbound⟩ := smoothing_bound_of_dyadic_bounds f hp hmem hw₀ hw hC₀ hC₁
    (hlow f) (fun j ↦ hann j f)
  refine ⟨hmem,hsol,hbound.trans ?_⟩
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (show D ≤ D+1 by linarith)) le_rfl

/-- The source's logarithmic summation step: `B>A+1` is exactly the
summability condition, and there is no positive differential loss. -/
theorem localSmoothing_log_of_frequency_bounds {n : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) (s : ℝ) (A : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hfreq : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦
        frequencyHalfWave smoothingAnnularCutoff h z.2 f z.1) p (observationMeasure n) ≤
      ENNReal.ofReal (C * h^(-s) * (1+Real.log (1/h))^A) * eLpNorm f p volume)
    {B : ℝ} (hB : (A : ℝ)+1 < B) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hlow : ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ frequencyHalfWave smoothingLowCutoff 1 z.2 f z.1)
        p (observationMeasure n) ≤ ENNReal.ofReal C₀ * eLpNorm (logBesselPotential s B f) p volume) :
    ∃ D : ℝ, 0 < D ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (logBesselPotential s B f) p volume ∧
      MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) p (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) p (observationMeasure n) ≤
        ENNReal.ofReal D * eLpNorm (logBesselPotential s B f) p volume := by
  obtain ⟨C₁,hC₁,hann⟩ := smoothing_dyadic_log_estimate hp hpt s A hC hfreq B
  let w : ℕ → ℝ := fun j ↦ smoothingDyadicLog j ^ A * smoothingDyadicLog j ^ (-B)
  have hw₀ (j : ℕ) : 0 ≤ w j := mul_nonneg
    (pow_nonneg (smoothingDyadicLog_pos j).le _)
    (Real.rpow_nonneg (smoothingDyadicLog_pos j).le _)
  have hw : Summable w := summable_smoothing_log_weights A hB
  let D : ℝ := C₀ + C₁ * ∑' j, w j
  have hD : 0 ≤ D := add_nonneg hC₀ (mul_nonneg hC₁ (tsum_nonneg hw₀))
  refine ⟨D+1, by linarith, ?_⟩
  intro f
  have hmem := OAI.Analysis.Fourier.BesselPotential.memLp_logBesselPotential s B f p
  obtain ⟨hsol,hbound⟩ := smoothing_bound_of_dyadic_bounds f hp hmem hw₀ hw hC₀ hC₁
    (hlow f) (fun j ↦ hann j f)
  refine ⟨hmem,hsol,hbound.trans ?_⟩
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (show D ≤ D+1 by linarith)) le_rfl

end OAI.Analysis.Fourier.LocalSmoothing
