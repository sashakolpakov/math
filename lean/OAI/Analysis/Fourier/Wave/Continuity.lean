import OAI.Analysis.Fourier.Wave.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open _root_.MeasureTheory
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Wave

theorem waveL2_norm_sq_integral {n : ℕ} (f : WaveL2 n) :
    ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  calc
    ‖f‖ ^ 2 = inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫ ξ, inner ℝ (f ξ) (f ξ) := rfl
    _ = _ := by simp_rw [real_inner_self_eq_norm_sq]

private theorem continuous_wavePhase_time {n : ℕ} (ξ : Space n) :
    Continuous (fun t : ℝ ↦ wavePhase t ξ) := by
  unfold wavePhase
  fun_prop

theorem continuous_phaseMultiply {n : ℕ} (f : WaveL2 n) :
    Continuous (fun t : ℝ ↦ phaseMultiply t f) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hi : Integrable (fun ξ ↦ ‖f ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hc : Continuous (fun t : ℝ ↦
      ∫ ξ, ‖wavePhase t ξ * f ξ - wavePhase s ξ * f ξ‖ ^ 2) := by
    apply continuous_of_dominated (bound := fun ξ ↦ 4 * ‖f ξ‖ ^ 2)
    · intro t
      exact (((continuous_wavePhase t).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f)).sub
        ((continuous_wavePhase s).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f))).norm.aemeasurable.pow_const 2 |>.aestronglyMeasurable
    · intro t
      exact Filter.Eventually.of_forall fun ξ ↦ by
        have hb := norm_sub_le (wavePhase t ξ * f ξ) (wavePhase s ξ * f ξ)
        simp only [norm_mul, norm_wavePhase, one_mul] at hb
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [norm_nonneg (wavePhase t ξ * f ξ - wavePhase s ξ * f ξ)]
    · exact hi.const_mul 4
    · exact Filter.Eventually.of_forall fun ξ ↦
        (((continuous_wavePhase_time ξ).mul continuous_const).sub
          continuous_const).norm.pow 2
  have heq : ∀ t : ℝ, ‖phaseMultiply t f - phaseMultiply s f‖ ^ 2 =
      ∫ ξ, ‖wavePhase t ξ * f ξ - wavePhase s ξ * f ξ‖ ^ 2 := by
    intro t
    rw [waveL2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (phaseMultiply t f) (phaseMultiply s f),
      phaseMultiply_coe t f, phaseMultiply_coe s f] with ξ h h₁ h₂
    simp only [h, Pi.sub_apply, h₁, h₂]
  have hnorm : Continuous (fun t : ℝ ↦ ‖phaseMultiply t f - phaseMultiply s f‖) := by
    have hh := Real.continuous_sqrt.comp hc
    convert hh using 1
    funext t
    simp only [Function.comp_apply, ← heq, Real.sqrt_sq (norm_nonneg _)]
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_self, norm_zero] using hnorm.tendsto s

theorem continuous_halfWaveL2 {n : ℕ} (f : WaveL2 n) :
    Continuous (fun t : ℝ ↦ halfWaveL2 t f) :=
  (Lp.fourierTransformₗᵢ (Space n) ℂ).symm.continuous.comp
    (continuous_phaseMultiply ((Lp.fourierTransformₗᵢ (Space n) ℂ) f))

end OAI.Analysis.Fourier.Wave
