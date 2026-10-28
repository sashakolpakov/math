import OAI.Analysis.Fourier.Restriction.WeightDilation
import OAI.Analysis.Fourier.Restriction.Modulation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def translatedFrequencyBump {n : ℕ} (f : Space n → ℂ) (R : ℝ) (v : Space n) : Space n → ℂ :=
  restrictionModulate (-v) (fun x ↦ f (R⁻¹ • x))

theorem angularFourier_translatedFrequencyBump {n : ℕ} (f : Space n → ℂ) {R : ℝ}
    (hR : 0 < R) (v ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (translatedFrequencyBump f R v) ξ =
      (R ^ n : ℝ) • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (R • (ξ - v)) := by
  rw [translatedFrequencyBump, angularFourier_restrictionModulate,
    OAI.Analysis.Fourier.BochnerRiesz.angularFourier_dilate f (inv_pos.mpr hR)]
  simp only [inv_pow, inv_inv, sub_eq_add_neg]

theorem norm_translatedFrequencyBump {n : ℕ} (f : Space n → ℂ) (R : ℝ) (v x : Space n) :
    ‖translatedFrequencyBump f R v x‖ = ‖f (R⁻¹ • x)‖ := norm_restrictionModulate _ _ _

theorem integrable_translatedFrequencyBump {n : ℕ} {f : Space n → ℂ} (hf : Integrable f)
    {R : ℝ} (hR : 0 < R) (v : Space n) : Integrable (translatedFrequencyBump f R v) :=
  integrable_restrictionModulate _ (hf.comp_smul (inv_ne_zero hR.ne'))

theorem translatedFrequencyBump_weight_bound {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {R a : ℝ} (hR : 1 ≤ R) (ha : 0 ≤ a) (v : Space n) :
    Integrable (fun x ↦ ‖translatedFrequencyBump f R v x‖ * (1 + ‖x‖) ^ a) ∧
    (∫ x, ‖translatedFrequencyBump f R v x‖ * (1 + ‖x‖) ^ a) ≤
      (R ^ n * R ^ a) * ∫ x, ‖f x‖ * (1 + ‖x‖) ^ a := by
  simp only [norm_translatedFrequencyBump]
  exact dilated_schwartz_weight_bound f hR ha

end OAI.Analysis.Fourier.Restriction
