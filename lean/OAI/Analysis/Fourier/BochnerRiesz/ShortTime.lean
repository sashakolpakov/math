import OAI.Analysis.Fourier.BochnerRiesz.Multiplier
import OAI.Analysis.Fourier.LocalSmoothing.L2

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff Topology

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def shortTimeWaveSymbol {n : ℕ} (χ : Space n → ℂ) (z : ℝ × Space n) : ℂ :=
  Complex.exp (-Complex.I * (z.1 * ‖z.2‖ : ℝ)) * χ z.2

theorem tsupport_shortTimeWaveSymbol {n : ℕ} (χ : Space n → ℂ) :
    tsupport (shortTimeWaveSymbol χ) ⊆ Set.univ ×ˢ tsupport χ := by
  intro z hz
  refine ⟨trivial, ?_⟩
  exact tsupport_comp_subset_preimage χ continuous_snd
    (tsupport_mul_subset_right (f := fun z : ℝ × Space n ↦
      Complex.exp (-Complex.I * (z.1 * ‖z.2‖ : ℝ))) hz)

theorem contDiff_shortTimeWaveSymbol {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hzero : (0 : Space n) ∉ tsupport χ) :
    ContDiff ℝ ∞ (shortTimeWaveSymbol χ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.2 ∈ tsupport χ
  · have hx : z.2 ≠ 0 := by intro h; exact hzero (h ▸ hz)
    have hn : ContDiffAt ℝ ∞ (fun z : ℝ × Space n ↦ ‖z.2‖) z :=
      ContDiffAt.norm (𝕜 := ℝ) contDiffAt_snd hx
    have hr := contDiffAt_fst.mul hn
    have hp : ContDiffAt ℝ ∞ (fun z : ℝ × Space n ↦
        -Complex.I * (z.1 * ‖z.2‖ : ℝ)) z :=
      contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp z hr)
    exact (Complex.contDiff_exp.contDiffAt.comp z hp).mul
      (hχ.contDiffAt.comp z contDiffAt_snd)
  · have hnear := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto (continuous_snd.tendsto z)
    have heq : shortTimeWaveSymbol χ =ᶠ[𝓝 z] (fun _ ↦ 0) := by
      filter_upwards [hnear] with q hq
      change χ q.2 = 0 at hq
      simp [shortTimeWaveSymbol, hq]
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem halfWave_eq_shortTime_multiplier {n : ℕ} (χ : Space n → ℂ)
    {h : ℝ} (hh : 0 < h) (τ : ℝ) (f : Space n → ℂ)
    (hcut : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (τ * h) f =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ shortTimeWaveSymbol χ (τ, ξ)) h 0 f := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave
  congr 1
  funext ξ
  by_cases hz : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = 0
  · simp [hz]
  have he : τ * ‖h • ξ‖ = τ * h * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    ring
  simp [shortTimeWaveSymbol, he, hcut ξ hz]

theorem shortTime_annular_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ τ ∈ Set.Icc (-2 : ℝ) 2,
      ∀ f : Space n → ℂ, Integrable f →
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (τ * h) f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume := by
  obtain ⟨C, hC, hb⟩ := uniform_frequencyHalfWave_zero_bound isCompact_Icc hc
    (contDiff_shortTimeWaveSymbol hχ hzero) (tsupport_shortTimeWaveSymbol χ)
  refine ⟨C, hC, ?_⟩
  intro h hh τ hτ f hf hcut p hp hptop
  rw [halfWave_eq_shortTime_multiplier χ hh τ f hcut]
  exact hb τ hτ h hh f hf p hp hptop

end OAI.Analysis.Fourier.BochnerRiesz
