import OAI.Analysis.Fourier.BochnerRiesz.FourierLimit
import OAI.Analysis.Fourier.SquareFunction.ConvolutionDensity

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def complexDualityPartner (p : ℝ) (z : ℂ) : ℂ := ‖z‖ ^ (p - 2) • star z

theorem measurable_complexDualityPartner (p : ℝ) : Measurable (complexDualityPartner p) := by
  unfold complexDualityPartner
  fun_prop

theorem norm_complexDualityPartner {p : ℝ} (hp : 1 < p) (z : ℂ) :
    ‖complexDualityPartner p z‖ = ‖z‖ ^ (p - 1) := by
  by_cases hz : z = 0
  · simp [complexDualityPartner, hz, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  calc
    _ = ‖z‖ ^ (p - 2) * ‖z‖ := by
      simp only [complexDualityPartner, norm_smul, norm_star, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    _ = ‖z‖ ^ (p - 2) * ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = ‖z‖ ^ (p - 1) := by rw [← Real.rpow_add hn]; congr 1 ; ring

theorem complexDualityPartner_mul {p : ℝ} (hp : 1 < p) (z : ℂ) :
    complexDualityPartner p z * z = Complex.ofReal (‖z‖ ^ p) := by
  by_cases hz : z = 0
  · simp [complexDualityPartner, hz, Real.zero_rpow (by linarith : p ≠ 0)]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [complexDualityPartner, Complex.real_smul, mul_assoc]
  change Complex.ofReal (‖z‖ ^ (p - 2)) * (star z * z) = _
  rw [show star z * z = Complex.ofReal (‖z‖ ^ 2) by simpa using Complex.conj_mul' z,
    ← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_add hn]
  congr 1
  norm_num

theorem aestronglyMeasurable_complexDualityPartner {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : AEStronglyMeasurable f μ) (p : ℝ) :
    AEStronglyMeasurable (fun x ↦ complexDualityPartner p (f x)) μ :=
  ((measurable_complexDualityPartner p).comp_aemeasurable hf.aemeasurable).aestronglyMeasurable

theorem eLpNorm_complexDualityPartner {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 < p) :
    eLpNorm (fun x ↦ complexDualityPartner p (f x)) (ENNReal.ofReal (p / (p - 1))) μ =
      eLpNorm f (ENNReal.ofReal p) μ ^ (p - 1) := by
  have he : ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (p - 1) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ (by linarith)]
  rw [← he, ← eLpNorm_norm_rpow f hf (show 0 < p - 1 by linarith)]
  rw [← eLpNorm_norm (fun x ↦ complexDualityPartner p (f x))
    (aestronglyMeasurable_complexDualityPartner hf p)]
  congr 1
  funext x
  exact norm_complexDualityPartner hp (f x)

end OAI.Analysis.Fourier.BochnerRiesz
