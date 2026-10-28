import OAI.Analysis.Fourier.SquareFunction.Square.Function
import OAI.Analysis.Fourier.SquareFunction.Radius.Dyadic
import OAI.Analysis.Fourier.SquareFunction.FourierDilation

open OAI.Analysis.Fourier.Wave

/-! Exact dyadic-radius reduction of the manuscript's Stein square function. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal

theorem radiusDerivativeCycles_dilate {n : ℕ} (α s : ℝ) {a : ℝ} (ha : 0 < a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    radiusDerivativeCycles α s
        (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne') f) (a • x) =
      radiusDerivativeCycles α (a * s) f x := by
  unfold radiusDerivativeCycles
  change 𝓕⁻ (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ s : ℂ) *
    𝓕 (fun y => f (a⁻¹ • y)) ξ) (a • x) = _
  rw [fourierMultiplier_dilate_cycles _ f (inv_pos.mpr ha), inv_smul_smul₀ ha.ne']
  apply congrArg (fun m : Space n → ℂ => 𝓕⁻ m x)
  funext ξ
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  have he := radiusMultiplier_scale ha α (a⁻¹ * ‖ξ‖) s
  rw [mul_inv_cancel_left₀ ha.ne'] at he
  rw [he, SchwartzMap.fourier_coe]

theorem steinSquareFunction_le_dyadic_radius_norms {n : ℕ} (α : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x ≤
      (∑' k : ℤ, eLpNorm (fun s => radiusDerivativeCycles α ((2 : ℝ) ^ k * s) f x)
        2 (volume.restrict (Icc (1 : ℝ) 2)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hm := measurable_first_section (measurable_radiusDerivativeCycles α f) x
  have hb := radius_square_dyadic_bound (fun r => radiusDerivativeCycles α r f x) hm
  rw [steinSquareFunction_eq_cycles]
  simp only [ENNReal.rpow_two] at hb ⊢
  exact hb

end OAI.Analysis.Fourier.SquareFunction
