import OAI.Analysis.Fourier.SquareFunction.Pointwise

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction

def radiusPhase (t s : ℝ) : ℂ :=
  Complex.exp ((-2 * Real.pi * s * t : ℝ) * Complex.I)

@[simp] theorem norm_radiusPhase (t s : ℝ) : ‖radiusPhase t s‖ = 1 := by
  simp [radiusPhase, Complex.norm_exp]

theorem measurable_radiusPhase (t : ℝ) : Measurable (radiusPhase t) := by
  unfold radiusPhase
  fun_prop

theorem radiusPhase_add (t a b : ℝ) :
    radiusPhase t (a + b) = radiusPhase t a * radiusPhase t b := by
  rw [radiusPhase, radiusPhase, radiusPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem radiusPhase_mul (t a b : ℝ) : radiusPhase t (a * b) = radiusPhase (a * t) b := by
  unfold radiusPhase
  congr 1
  push_cast
  ring

theorem fourier_eq_radiusPhase (φ : ℝ → ℂ) (t : ℝ) :
    𝓕 φ t = ∫ s, radiusPhase t s * φ s := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rfl

theorem integral_radius_shift_dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℝ → E) (b δ : ℝ) :
    (∫ s, φ ((s - b) / δ)) = |δ| • ∫ s, φ s := by
  rw [integral_sub_right_eq_self (fun s => φ (s / δ)) b, Measure.integral_comp_div]

theorem integrable_radius_shift_dilate {φ : ℝ → ℂ} (hφ : Integrable φ)
    (b : ℝ) {δ : ℝ} (hδ : δ ≠ 0) :
    Integrable (fun s => φ ((s - b) / δ)) :=
  (hφ.comp_div hδ).comp_sub_right b

/-- Fourier transformation of a translated and dilated radius cutoff. -/
theorem fourier_radius_shift_dilate (φ : ℝ → ℂ) (b t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    𝓕 (fun s => φ ((s - b) / δ)) t =
      (δ : ℂ) * radiusPhase t b * 𝓕 φ (δ * t) := by
  rw [fourier_eq_radiusPhase, fourier_eq_radiusPhase]
  have he (s : ℝ) : radiusPhase t s * φ ((s - b) / δ) =
      radiusPhase t b * (radiusPhase (δ * t) ((s - b) / δ) * φ ((s - b) / δ)) := by
    have hp : radiusPhase t s = radiusPhase t b * radiusPhase (δ * t) ((s - b) / δ) := by
      rw [← radiusPhase_mul, mul_div_cancel₀ _ hδ.ne', ← radiusPhase_add]
      congr 1
      ring
    rw [hp, mul_assoc]
  simp_rw [he]
  rw [integral_const_mul,
    integral_radius_shift_dilate (fun s => radiusPhase (δ * t) s * φ s) b δ, abs_of_pos hδ,
    Complex.real_smul]
  ring

section Superposition

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]

theorem fourier_integral_swap {G : ℝ × X → ℂ} (hG : Integrable G (volume.prod μ))
    (t : ℝ) :
    𝓕 (fun s => ∫ ξ, G (s, ξ) ∂μ) t = ∫ ξ, 𝓕 (fun s => G (s, ξ)) t ∂μ := by
  have ht : Integrable (fun z : ℝ × X => radiusPhase t z.1 * G z) (volume.prod μ) := by
    apply hG.mono
      (((measurable_radiusPhase t).comp measurable_fst).aestronglyMeasurable.mul
        hG.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun z => by simp
  simp_rw [fourier_eq_radiusPhase, ← integral_const_mul]
  exact integral_integral_swap ht

def radiusSuperposition (φ : ℝ → ℂ) (δ : ℝ) (R : X → ℝ) (a : X → ℂ) (s : ℝ) : ℂ :=
  ∫ ξ, φ ((s - R ξ) / δ) * a ξ ∂μ

omit [SFinite μ] in
theorem integrable_radiusSuperposition_kernel (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) {R : X → ℝ} (hR : Measurable R)
    {a : X → ℂ} (ham : Measurable a) (ha : Integrable a μ) :
    Integrable (fun z : X × ℝ => φ ((z.2 - R z.1) / δ) * a z.1) (μ.prod volume) := by
  have hm : Measurable (fun z : X × ℝ => φ ((z.2 - R z.1) / δ) * a z.1) :=
    (φ.continuous.measurable.comp
      ((measurable_snd.sub (hR.comp measurable_fst)).div_const δ)).mul
        (ham.comp measurable_fst)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun ξ =>
      (integrable_radius_shift_dilate (φ.integrable) (R ξ) hδ.ne').mul_const (a ξ)
  · have he (ξ : X) : (∫ s : ℝ, ‖φ ((s - R ξ) / δ) * a ξ‖) =
        (δ * ∫ s : ℝ, ‖φ s‖) * ‖a ξ‖ := by
      simp_rw [norm_mul]
      rw [integral_mul_const,
        integral_radius_shift_dilate (fun s : ℝ => ‖φ s‖) (R ξ) δ,
        abs_of_pos hδ, smul_eq_mul]
    simpa only [he] using ha.norm.const_mul (δ * ∫ s : ℝ, ‖φ s‖)

theorem integrable_radiusSuperposition (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) {R : X → ℝ} (hR : Measurable R)
    {a : X → ℂ} (ham : Measurable a) (ha : Integrable a μ) :
    Integrable (radiusSuperposition μ φ δ R a) :=
  (integrable_radiusSuperposition_kernel μ φ hδ hR ham ha).integral_prod_right

omit [SFinite μ] in
theorem norm_radiusSuperposition_le (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (R : X → ℝ)
    {a : X → ℂ} (ha : Integrable a μ) (s : ℝ) :
    ‖radiusSuperposition μ φ δ R a s‖ ≤
      SchwartzMap.seminorm ℝ 0 0 φ * ∫ ξ, ‖a ξ‖ ∂μ := by
  unfold radiusSuperposition
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (ha.norm.const_mul _)
  exact Filter.Eventually.of_forall fun ξ => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ φ _) (norm_nonneg _)

theorem memLp_radiusSuperposition (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) {R : X → ℝ} (hR : Measurable R)
    {a : X → ℂ} (ham : Measurable a) (ha : Integrable a μ) :
    MemLp (radiusSuperposition μ φ δ R a) 2 := by
  have hi := integrable_radiusSuperposition μ φ hδ hR ham ha
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).2
  have hm : AEStronglyMeasurable (fun s => ‖radiusSuperposition μ φ δ R a s‖ ^ 2) volume := by
    simp_rw [pow_two]
    exact hi.aestronglyMeasurable.norm.mul hi.aestronglyMeasurable.norm
  apply (hi.norm.const_mul (SchwartzMap.seminorm ℝ 0 0 φ * ∫ ξ, ‖a ξ‖ ∂μ)).mono'
    hm
  exact Filter.Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul_of_nonneg_right (norm_radiusSuperposition_le μ φ δ R ha s) (norm_nonneg _)

/-- The exact radius-Fourier identity underlying the thin-shell argument.
All integrals are ordinary Bochner integrals, and product integrability is proved. -/
theorem fourier_radiusSuperposition (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) {R : X → ℝ} (hR : Measurable R)
    {a : X → ℂ} (ham : Measurable a) (ha : Integrable a μ) (t : ℝ) :
    𝓕 (radiusSuperposition μ φ δ R a) t =
      (δ : ℂ) * 𝓕 (φ : ℝ → ℂ) (δ * t) *
        ∫ ξ, radiusPhase t (R ξ) * a ξ ∂μ := by
  have hk : Integrable (fun z : ℝ × X => φ ((z.1 - R z.2) / δ) * a z.2)
      (volume.prod μ) :=
    (integrable_radiusSuperposition_kernel μ φ hδ hR ham ha).swap
  change 𝓕 (fun s => ∫ ξ, φ ((s - R ξ) / δ) * a ξ ∂μ) t = _
  rw [fourier_integral_swap μ hk]
  have he (ξ : X) : 𝓕 (fun s => φ ((s - R ξ) / δ) * a ξ) t =
      ((δ : ℂ) * 𝓕 (φ : ℝ → ℂ) (δ * t)) * (radiusPhase t (R ξ) * a ξ) := by
    rw [fourier_eq_radiusPhase]
    simp_rw [← mul_assoc]
    rw [integral_mul_const, ← fourier_eq_radiusPhase,
      fourier_radius_shift_dilate (φ : ℝ → ℂ) (R ξ) t hδ]
    ring
  simp_rw [he]
  exact integral_const_mul _ _

end Superposition

end OAI.Analysis.Fourier.SquareFunction
