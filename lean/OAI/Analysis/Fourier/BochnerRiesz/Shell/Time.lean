import OAI.Analysis.Fourier.BochnerRiesz.ScaledTime

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- The time scale dual to a shell of thickness `δ`. The frequency support
is in a fixed annulus, so the only loss is `δ^(-σ-1/p)`. -/
theorem localSmoothing_shell_time (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {p ε M : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hM : 1 / p + (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ ξ = 1) →
      MemLp (fun z : Space n × ℝ ↦ (1 + |δ * z.2|) ^ (-M) • OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (volume.prod volume) ∧
      eLpNorm (fun z : Space n × ℝ ↦ (1 + |δ * z.2|) ^ (-M) • OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (volume.prod volume) ≤
      ENNReal.ofReal (C * δ ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) - 1 / p)) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := localSmoothing_weighted_time_scale hls hn hχ hc hzero hp hε hM
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδone f hcut
  have hR : (1 : ℝ) ≤ δ⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hδ).mpr (by simpa using hδone)
  have H := hb 1 δ⁻¹ zero_lt_one hR f (by simpa only [one_smul] using hcut)
  have heq : scaledWeightedTimeFunction M δ⁻¹ (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) =
      (fun z : Space n × ℝ ↦ (1 + |δ * z.2|) ^ (-M) • OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) := by
    funext z
    simp [scaledWeightedTimeFunction, div_inv_eq_mul, mul_comm]
  have hpow : C * (δ⁻¹) ^ (1 / p) * (1 / δ⁻¹) ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)) =
      C * δ ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) - 1 / p) := by
    rw [one_div (δ⁻¹), inv_inv, Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le]
    rw [mul_assoc, ← Real.rpow_add hδ]
    congr 2
    ring
  simpa only [heq, hpow] using H

end OAI.Analysis.Fourier.BochnerRiesz
