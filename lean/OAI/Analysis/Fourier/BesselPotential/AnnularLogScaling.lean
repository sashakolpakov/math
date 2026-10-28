import OAI.Analysis.Fourier.BesselPotential.AnnularLogSymbol

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace OAI.Analysis.Fourier.BesselPotential

def annularLogScale (h : ℝ) : ℝ := 1+Real.log (1/h)

def annularLogParameter (h : ℝ) : ℝ × ℝ :=
  (Real.sqrt h,Real.arcsin (Real.sqrt (annularLogScale h)⁻¹))

theorem annularLogScale_one_le {h : ℝ} (hh : 0 < h) (hone : h ≤ 1) :
    1 ≤ annularLogScale h := by
  have hi : 1 ≤ 1/h := (le_div_iff₀ hh).mpr (by simpa using hone)
  exact le_add_of_nonneg_right (Real.log_nonneg hi)

theorem annularLogParameter_mem {h : ℝ} (_ : 0 < h) (hone : h ≤ 1) :
    annularLogParameter h ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) (Real.pi/2) := by
  refine ⟨⟨Real.sqrt_nonneg h,?_⟩,
    ⟨Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _),Real.arcsin_le_pi_div_two _⟩⟩
  change Real.sqrt h ≤ 1
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hone

theorem annularLogParameter_sin_sq {h : ℝ} (hh : 0 < h) (hone : h ≤ 1) :
    Real.sin (annularLogParameter h).2 ^ 2 = (annularLogScale h)⁻¹ := by
  have hL := annularLogScale_one_le hh hone
  have hi : 0 ≤ (annularLogScale h)⁻¹ := inv_nonneg.mpr (by linarith)
  have his : (annularLogScale h)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  have hs : Real.sqrt (annularLogScale h)⁻¹ ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt his
  dsimp only [annularLogParameter]
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((annularLogScale h)⁻¹)]) hs,
    Real.sq_sqrt hi]

theorem annularLogParameter_radial {n : ℕ} {h : ℝ} (hh : 0 < h) (ξ : Space n) :
    (annularLogParameter h).1^4 + ‖h • ξ‖^2 = h^2 * (1+‖ξ‖^2) := by
  have hs : (Real.sqrt h)^4 = h^2 := by
    calc
      (Real.sqrt h)^4 = ((Real.sqrt h)^2)^2 := by ring
      _ = h^2 := by rw [Real.sq_sqrt hh.le]
  dsimp only [annularLogParameter]
  rw [hs,norm_smul,Real.norm_eq_abs,abs_of_pos hh]
  ring

theorem annularLogBase_scaling {n : ℕ} {h : ℝ} (hh : 0 < h) (ξ : Space n) :
    annularLogBase (annularLogParameter h,h • ξ) =
      Real.log h + Real.log (2+Real.sqrt (1+‖ξ‖^2)) := by
  unfold annularLogBase
  rw [annularLogParameter_radial hh]
  change Real.log (2*(Real.sqrt h)^2 + Real.sqrt (h^2*(1+‖ξ‖^2))) = _
  rw [Real.sq_sqrt hh.le,Real.sqrt_mul (sq_nonneg h),Real.sqrt_sq hh.le]
  have he : 2*h+h*Real.sqrt (1+‖ξ‖^2) = h*(2+Real.sqrt (1+‖ξ‖^2)) := by ring
  rw [he,Real.log_mul hh.ne' (by positivity)]

theorem annularLogBlend_scaling {n : ℕ} {h : ℝ} (hh : 0 < h) (hone : h ≤ 1)
    (ξ : Space n) :
    annularLogBlend (annularLogParameter h,h • ξ) =
      Real.log (2+Real.sqrt (1+‖ξ‖^2)) / annularLogScale h := by
  have hs := annularLogParameter_sin_sq hh hone
  have hc : Real.cos (annularLogParameter h).2^2 = 1-(annularLogScale h)⁻¹ := by
    linarith [Real.cos_sq_add_sin_sq (annularLogParameter h).2]
  have hscale : annularLogScale h = 1-Real.log h := by
    simp [annularLogScale,one_div,Real.log_inv,sub_eq_add_neg]
  have hne : annularLogScale h ≠ 0 := ne_of_gt (by linarith [annularLogScale_one_le hh hone])
  dsimp only [annularLogBlend]
  rw [hc,hs,annularLogBase_scaling hh]
  field_simp
  nlinarith

end OAI.Analysis.Fourier.BesselPotential
