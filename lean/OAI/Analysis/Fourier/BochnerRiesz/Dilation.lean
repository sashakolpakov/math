import OAI.Analysis.Fourier.Wave.AngularTransform

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem angularFourier_dilate {n : ℕ} (f : Space n → ℂ) {r : ℝ} (hr : 0 < r)
    (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f (r • x)) ξ = (r ^ n)⁻¹ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (r⁻¹ • ξ) := by
  have hchange := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun y ↦ Complex.exp (-Complex.I * ((inner ℝ y (r⁻¹ • ξ) : ℝ) : ℂ)) * f y)
    r (hR := hr.le)
  have hid (x : Space n) : inner ℝ (r • x) (r⁻¹ • ξ) = inner ℝ x ξ := by
    rw [real_inner_smul_left, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  simpa only [OAI.Analysis.Fourier.LocalSmoothing.angularFourier, hid, Space, finrank_euclideanSpace_fin] using hchange

theorem angularInverse_dilate {n : ℕ} (g : Space n → ℂ) {r : ℝ} (hr : 0 < r)
    (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ g (r • ξ)) x = (r ^ n)⁻¹ • OAI.Analysis.Fourier.LocalSmoothing.angularInverse g (r⁻¹ • x) := by
  have hchange := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun ξ ↦ Complex.exp (Complex.I * ((inner ℝ (r⁻¹ • x) ξ : ℝ) : ℂ)) * g ξ)
    r (hR := hr.le)
  have hid (ξ : Space n) : inner ℝ (r⁻¹ • x) (r • ξ) = inner ℝ x ξ := by
    rw [real_inner_smul_left, inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  simp only [hid, Space, finrank_euclideanSpace_fin] at hchange
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse]
  rw [hchange]
  exact smul_comm _ _ _

theorem angularInverse_smul_real {n : ℕ} (c : ℝ) (g : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ c • g ξ) x = c • OAI.Analysis.Fourier.LocalSmoothing.angularInverse g x := by
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse, mul_smul_comm, integral_smul]
  exact smul_comm _ _ _

/-- Space and time have the same scaling for the exact angular half-wave
integral. All Fourier Jacobian factors cancel. -/
theorem halfWaveIntegral_dilate {n : ℕ} (f : Space n → ℂ) {r : ℝ} (hr : 0 < r)
    (t : ℝ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t (fun y ↦ f (r • y)) x = OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (r * t) f (r • x) := by
  let g : Space n → ℂ := fun ξ ↦ Complex.exp (-Complex.I * ((r * t) * ‖ξ‖ : ℝ)) *
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ
  have hphase (ξ : Space n) : (r * t) * ‖r⁻¹ • ξ‖ = t * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    field_simp
  have heq : (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
      OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun y ↦ f (r • y)) ξ) =
      (fun ξ ↦ (r ^ n)⁻¹ • g (r⁻¹ • ξ)) := by
    funext ξ
    rw [angularFourier_dilate f hr ξ]
    dsimp only [g]
    rw [hphase, mul_smul_comm]
  rw [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral, heq, angularInverse_smul_real,
    angularInverse_dilate g (inv_pos.mpr hr)]
  simp only [inv_pow, inv_inv, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_smul]
  rfl

/-- Real scalar dilation as a continuous linear equivalence. -/
def realDilationEquiv (n : ℕ) (r : ℝ) (hr : r ≠ 0) : Space n ≃L[ℝ] Space n where
  toFun x := r • x
  invFun x := r⁻¹ • x
  left_inv x := by simp [smul_smul, hr]
  right_inv x := by simp [smul_smul, hr]
  map_add' x y := smul_add _ _ _
  map_smul' c x := smul_comm _ _ _
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def schwartzDilate {n : ℕ} (r : ℝ) (hr : r ≠ 0) (f : SchwartzMap (Space n) ℂ) :
    SchwartzMap (Space n) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realDilationEquiv n r hr) f

@[simp] theorem schwartzDilate_apply {n : ℕ} (r : ℝ) (hr : r ≠ 0)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : schwartzDilate r hr f x = f (r • x) := rfl

theorem eLpNorm_dilate {n : ℕ} (f : Space n → ℂ) (hf : Measurable f) (p : ℝ≥0∞)
    {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x ↦ f (r • x)) p (volume : Measure (Space n)) =
      ENNReal.ofReal ((r ^ n)⁻¹) ^ (1 / p.toReal) * eLpNorm f p (volume : Measure (Space n)) := by
  have hcont : Continuous (fun x : Space n ↦ r • x) := by fun_prop
  have hm : AEMeasurable (fun x : Space n ↦ r • x) (volume : Measure (Space n)) :=
    hcont.measurable.aemeasurable
  have h := (eLpNorm_map_measure (p := p) (g := f) hf.aestronglyMeasurable hm).symm
  rw [Measure.map_addHaar_smul (volume : Measure (Space n)) hr.ne'] at h
  simp only [Space, finrank_euclideanSpace_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hr n))] at h
  rw [eLpNorm_smul_measure_of_ne_zero (by positivity) _ _ _] at h
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul] using h

theorem eLpNorm_schwartzDilate {n : ℕ} (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞)
    {r : ℝ} (hr : 0 < r) :
    eLpNorm (schwartzDilate r hr.ne' f) p (volume : Measure (Space n)) =
      ENNReal.ofReal ((r ^ n)⁻¹) ^ (1 / p.toReal) * eLpNorm f p (volume : Measure (Space n)) :=
  eLpNorm_dilate f f.continuous.measurable p hr

end OAI.Analysis.Fourier.BochnerRiesz
