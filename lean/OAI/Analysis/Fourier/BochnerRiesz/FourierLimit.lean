import OAI.Analysis.Fourier.SquareFunction.VectorConvolution
import OAI.Analysis.Fourier.BochnerRiesz.MaximalSummation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem tendsto_fourierInv_bounded_symbols {n : ℕ} {m : ℕ → Space n → ℂ} {mlimit g : Space n → ℂ}
    (hm : ∀ j, AEStronglyMeasurable (m j) volume) {C : ℝ}
    (hb : ∀ j ξ, ‖m j ξ‖ ≤ C) (hg : Integrable g)
    (hl : ∀ ξ, Tendsto (fun j ↦ m j ξ) atTop (𝓝 (mlimit ξ))) (x : Space n) :
    Tendsto (fun j ↦ 𝓕⁻ (fun ξ ↦ m j ξ * g ξ) x) atTop
      (𝓝 (𝓕⁻ (fun ξ ↦ mlimit ξ * g ξ) x)) := by
  simp only [OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul]
  apply tendsto_integral_of_dominated_convergence (fun ξ ↦ C * ‖g ξ‖)
  · intro j
    exact (OAI.Analysis.Fourier.SquareFunction.continuous_spatialPhase x).aestronglyMeasurable.smul ((hm j).mul hg.aestronglyMeasurable)
  · exact hg.norm.const_mul C
  · intro j
    exact Eventually.of_forall (fun ξ ↦ by
      simpa only [norm_smul, OAI.Analysis.Fourier.SquareFunction.norm_spatialPhase, one_mul, norm_mul] using
        mul_le_mul_of_nonneg_right (hb j ξ) (norm_nonneg (g ξ)))
  · exact Eventually.of_forall (fun ξ ↦ tendsto_const_nhds.smul ((hl ξ).mul tendsto_const_nhds))

theorem eLpNorm_le_of_tendsto_pointwise {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : ℕ → X → ℂ} {g : X → ℂ} (hf : ∀ j, AEStronglyMeasurable (f j) μ)
    (hg : AEStronglyMeasurable g μ) (hlim : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x)))
    {p : ℝ} (hp : 0 < p) {B : ℝ≥0∞}
    (hb : ∀ j, eLpNorm (f j) (ENNReal.ofReal p) μ ≤ B) :
    eLpNorm g (ENNReal.ofReal p) μ ≤ B := by
  have he (j : ℕ) : (∫⁻ x, ‖f j x‖ₑ ^ p ∂μ) ≤ B ^ p := by
    rw [← eLpNorm_rpow_eq_lintegral hp (hf j)]
    exact ENNReal.rpow_le_rpow (hb j) hp.le
  have H : (∫⁻ x, ‖g x‖ₑ ^ p ∂μ) ≤ B ^ p := by
    calc
      _ = ∫⁻ x, liminf (fun j ↦ ‖f j x‖ₑ ^ p) atTop ∂μ := by
        apply lintegral_congr
        intro x
        have ht : Tendsto (fun j ↦ ‖f j x‖ₑ ^ p) atTop (𝓝 (‖g x‖ₑ ^ p)) :=
          ENNReal.continuous_rpow_const.continuousAt.tendsto.comp
            (continuous_enorm.continuousAt.tendsto.comp (hlim x))
        exact ht.liminf_eq.symm
      _ ≤ liminf (fun j ↦ ∫⁻ x, ‖f j x‖ₑ ^ p ∂μ) atTop :=
        lintegral_liminf_le' (fun j ↦ (hf j).enorm.pow_const p)
      _ ≤ B ^ p := liminf_le_of_frequently_le (Frequently.of_forall he)
  rw [← eLpNorm_rpow_eq_lintegral hp hg] at H
  have H' := ENNReal.rpow_le_rpow H (le_of_lt (one_div_pos.mpr hp))
  simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] using H'

end OAI.Analysis.Fourier.BochnerRiesz
