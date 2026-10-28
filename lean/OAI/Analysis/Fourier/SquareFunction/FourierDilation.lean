import OAI.Analysis.Fourier.SquareFunction.KernelHilbert
import OAI.Analysis.Fourier.BochnerRiesz.Dilation

open OAI.Analysis.Fourier.Wave

/-! Exact spatial dilation for classical Fourier multipliers in the cycles
normalization used by the square-function kernels. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform

theorem fourier_dilate_cycles {n : ℕ} (f : Space n → ℂ) {r : ℝ} (hr : 0 < r)
    (ξ : Space n) :
    𝓕 (fun x => f (r • x)) ξ = (r ^ n)⁻¹ • 𝓕 f (r⁻¹ • ξ) := by
  rw [← OAI.Analysis.Fourier.Wave.angularFourier_scaled, OAI.Analysis.Fourier.BochnerRiesz.angularFourier_dilate f hr,
    smul_comm r⁻¹ (2 * Real.pi) ξ, OAI.Analysis.Fourier.Wave.angularFourier_scaled]

theorem fourierInv_dilate_cycles {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] (g : Space n → H)
    {r : ℝ} (hr : 0 < r) (x : Space n) :
    𝓕⁻ (fun ξ => g (r • ξ)) x = (r ^ n)⁻¹ • 𝓕⁻ g (r⁻¹ • x) := by
  have hid (ξ : Space n) : spatialPhase (r⁻¹ • x) (r • ξ) = spatialPhase x ξ := by
    unfold spatialPhase
    rw [real_inner_smul_left, inner_smul_right]
    congr 3
    field_simp
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun ξ => spatialPhase (r⁻¹ • x) ξ • g ξ) r (hR := hr.le)
  simpa only [hid, Space, finrank_euclideanSpace_fin, fourierInv_eq_spatialPhase_smul] using h

theorem fourierInv_smul_real_cycles {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] (g : Space n → H) (c : ℝ) (x : Space n) :
    𝓕⁻ (fun ξ => c • g ξ) x = c • 𝓕⁻ g x := by
  rw [fourierInv_eq_spatialPhase_smul, fourierInv_eq_spatialPhase_smul, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  exact smul_comm _ _ _

theorem fourierMultiplier_dilate_cycles {n : ℕ} (m f : Space n → ℂ)
    {r : ℝ} (hr : 0 < r) (x : Space n) :
    𝓕⁻ (fun ξ => m ξ * 𝓕 (fun y => f (r • y)) ξ) x =
      𝓕⁻ (fun ξ => m (r • ξ) * 𝓕 f ξ) (r • x) := by
  let g : Space n → ℂ := fun ξ => m (r • ξ) * 𝓕 f ξ
  have he : (fun ξ => m ξ * 𝓕 (fun y => f (r • y)) ξ) =
      fun ξ => (r ^ n)⁻¹ • g (r⁻¹ • ξ) := by
    funext ξ
    rw [fourier_dilate_cycles f hr]
    simp only [g, smul_inv_smul₀ hr.ne', Complex.real_smul]
    ring
  rw [he]
  rw [fourierInv_smul_real_cycles]
  rw [fourierInv_dilate_cycles g (inv_pos.mpr hr)]
  simp only [inv_pow, inv_inv, smul_smul, inv_mul_cancel₀ (pow_ne_zero n hr.ne'), one_smul, g]

end OAI.Analysis.Fourier.SquareFunction
