import OAI.Analysis.Fourier.BochnerRiesz.InteriorSymbol

open OAI.Analysis.Fourier.Wave

open Set Metric Filter _root_.MeasureTheory
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem exterior_times_radial_cutoff {n : ℕ} (δ : ℝ) {J : ℕ} (hJ : 2 ≤ J)
    {χ : Space n → ℂ} (hχ : ∀ ξ, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 → χ ξ = 1) (ξ : Space n) :
    brExteriorSymbol δ χ ξ * (((max (1 - ‖ξ‖) 0) ^ δ *
      radialPartitionCutoff ((2 : ℝ) ^ J * (1 - ‖ξ‖))) : ℝ) =
      ((OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ * radialPartitionCutoff ((2 : ℝ) ^ J * (1 - ‖ξ‖))) : ℝ) := by
  by_cases hz : radialPartitionCutoff ((2 : ℝ) ^ J * (1 - ‖ξ‖)) = 0
  · simp only [hz, mul_zero, Complex.ofReal_zero]
  · obtain ⟨hlo, hhi⟩ := radialCutoff_support_annulus hJ hz
    rw [brExteriorSymbol, hχ ξ hlo hhi, one_mul, bochnerRieszSymbol_unit_factor]
    simp only [Complex.ofReal_mul]
    ring

theorem hasSum_bochnerRiesz_symbol_shells {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {J : ℕ} (hJ : 2 ≤ J)
    {χ : Space n → ℂ} (hχ : ∀ ξ, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 → χ ξ = 1) (ξ : Space n) :
    HasSum (fun j : ℕ ↦ Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) * brExteriorSymbol δ χ ξ *
      dyadicPowerProfile δ ((2 : ℝ) ^ (J + j) * (1 - ‖ξ‖)))
      ((OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ : ℂ) - (brInteriorReal δ J ξ : ℂ)) := by
  have H := (Complex.hasSum_ofReal.mpr (hasSum_dyadicPower hδ (1 - ‖ξ‖) J)).mul_left
    (brExteriorSymbol δ χ ξ)
  have he : brExteriorSymbol δ χ ξ *
      (((max (1 - ‖ξ‖) 0) ^ δ * radialPartitionCutoff ((2 : ℝ) ^ J * (1 - ‖ξ‖))) : ℝ) =
      (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ : ℂ) - (brInteriorReal δ J ξ : ℂ) := by
    rw [exterior_times_radial_cutoff δ hJ hχ, brInteriorReal]
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he] at H
  convert H using 1
  ext j
  rw [dyadicPowerProfile_apply, Complex.ofReal_mul]
  ring

theorem bochnerRiesz_symbol_finite_partition {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) {χ : Space n → ℂ}
    (hχ : ∀ ξ, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 → χ ξ = 1) (N : ℕ) (ξ : Space n) :
    (brInteriorReal δ J ξ : ℂ) +
      ∑ j ∈ Finset.range N, Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) * brExteriorSymbol δ χ ξ *
        dyadicPowerProfile δ ((2 : ℝ) ^ (J + j) * (1 - ‖ξ‖)) =
      (brInteriorReal δ (J + N) ξ : ℂ) := by
  have hs : (∑ j ∈ Finset.range N, Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) * brExteriorSymbol δ χ ξ *
        dyadicPowerProfile δ ((2 : ℝ) ^ (J + j) * (1 - ‖ξ‖))) =
      brExteriorSymbol δ χ ξ *
        ((∑ j ∈ Finset.range N, ((2 : ℝ) ^ (J + j)) ^ (-δ) *
          positiveDyadicPower δ ((2 : ℝ) ^ (J + j) * (1 - ‖ξ‖))) : ℝ) := by
    simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.ofReal_mul, dyadicPowerProfile_apply]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs, dyadicPower_partial_sum_all hδ]
  rw [mul_sub, Complex.ofReal_sub, mul_sub]
  rw [exterior_times_radial_cutoff δ hJ hχ,
    exterior_times_radial_cutoff δ (show 2 ≤ J + N by omega) hχ]
  simp only [brInteriorReal, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

end OAI.Analysis.Fourier.BochnerRiesz
