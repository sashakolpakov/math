import OAI.Analysis.Fourier.Restriction.Sparse.Reconstruction
import OAI.Analysis.Fourier.Restriction.ThinLocal

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem sparse_annulus_width {R : ℝ} (hR : 1 ≤ R) :
    0 < (2 * R)⁻¹ ∧ (2 * R)⁻¹ ≤ 1 / 2 := by
  constructor
  · positivity
  · rw [← one_div]
    apply (div_le_iff₀ (by linarith : 0 < 2 * R)).mpr
    nlinarith

theorem sphericalAnnulus_subset_closedBall {n : ℕ} {δ : ℝ} (hδ : δ ≤ 1) :
    sphericalAnnulus (n := n) δ ⊆ closedBall 0 2 := by
  intro ξ hξ
  rw [mem_closedBall, dist_zero_right]
  change |‖ξ‖ - 1| ≤ δ at hξ
  have H := (abs_le.mp hξ).2
  linarith

theorem localizedFourierKernel_zero_off_annulus {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0)
    {R : ℝ} (hR : 0 < R) (z ω ξ : Space n) (hω : ‖ω‖ = 1)
    (hξ : ξ ∉ sphericalAnnulus ((2 * R)⁻¹)) :
    localizedFourierKernel u R z ω ξ = 0 := by
  rw [localizedFourierKernel_eq u hR, hs, mul_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have hd : |‖ξ‖ - 1| ≤ ‖ω - ξ‖ := by
    simpa only [hω, norm_sub_rev] using abs_norm_sub_norm_le ξ ω
  have hx : (2 * R)⁻¹ < |‖ξ‖ - 1| := by
    simpa only [sphericalAnnulus, Set.mem_ofPred_eq, not_le] using hξ
  have he : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by field_simp
  have H := mul_lt_mul_of_pos_left (hx.trans_le hd) hR
  rw [he] at H
  linarith

theorem localizedFourierKernel_annulus_reconstruction {n : ℕ} {f : Space n → ℂ}
    (hf : Integrable f) (u : SchwartzMap (Space n) ℂ)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0)
    {R : ℝ} (hR : 0 < R) (z ω : Space n) (hω : ‖ω‖ = 1) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f (x - z) * u (R⁻¹ • (x - z))) ω =
      (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
        ∫ ξ in sphericalAnnulus ((2 * R)⁻¹),
          localizedFourierKernel u R z ω ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  rw [localizedFourierKernel_reconstruction hf u hR z ω]
  congr 1
  rw [← integral_indicator (measurableSet_sphericalAnnulus _)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  by_cases hξ : ξ ∈ sphericalAnnulus ((2 * R)⁻¹)
  · rw [indicator_of_mem hξ]
  · rw [indicator_of_notMem hξ, localizedFourierKernel_zero_off_annulus u hs hR z ω ξ hω hξ,
      zero_mul]

end OAI.Analysis.Fourier.Restriction
