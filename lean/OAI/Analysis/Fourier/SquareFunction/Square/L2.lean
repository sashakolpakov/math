import OAI.Analysis.Fourier.SquareFunction.Basic
import OAI.Analysis.Fourier.SquareFunction.Multiplier

/-! The exact radius integral in the `p = 2` Stein square-function argument. -/

namespace OAI.Analysis.Fourier.SquareFunction

open Set _root_.MeasureTheory
open scoped ENNReal

lemma radius_substitution_image {ρ : ℝ} (hρ : 0 < ρ) :
    (fun r : ℝ => ρ ^ 2 / r ^ 2) '' Ioi ρ = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨r, hr, rfl⟩
    change ρ < r at hr
    have hrpos : 0 < r := hρ.trans hr
    refine ⟨div_pos (sq_pos_of_pos hρ) (sq_pos_of_pos hrpos), ?_⟩
    apply (div_lt_one (sq_pos_of_pos hrpos)).2
    nlinarith
  · intro hu
    have hs : 0 < Real.sqrt u := Real.sqrt_pos.2 hu.1
    have hs1 : Real.sqrt u < 1 := by
      nlinarith [Real.sq_sqrt hu.1.le, hu.2]
    refine ⟨ρ / Real.sqrt u, ?_, ?_⟩
    · apply (lt_div_iff₀ hs).2
      nlinarith
    · dsimp
      rw [div_pow]
      field_simp
      nlinarith [Real.sq_sqrt hu.1.le]

lemma radius_substitution_injective {ρ : ℝ} (hρ : 0 < ρ) :
    InjOn (fun r : ℝ => ρ ^ 2 / r ^ 2) (Ioi ρ) := by
  intro r hr s hs heq
  have hrpos : 0 < r := hρ.trans hr
  have hspos : 0 < s := hρ.trans hs
  have hsq : r ^ 2 = s ^ 2 := by
    have hcross := (div_eq_div_iff (ne_of_gt (sq_pos_of_pos hrpos))
      (ne_of_gt (sq_pos_of_pos hspos))).1 heq
    nlinarith [sq_pos_of_pos hρ]
  nlinarith

lemma hasDerivAt_radius_substitution {ρ r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => ρ ^ 2 / s ^ 2) (-2 * ρ ^ 2 / r ^ 3) r := by
  convert (hasDerivAt_const r (ρ ^ 2)).div (hasDerivAt_pow 2 r)
    (pow_ne_zero 2 hr) using 1
  field_simp
  ; ring

/-- The radial Plancherel integral is independent of the nonzero frequency. -/
theorem radius_integral {ρ α : ℝ} (hρ : 0 < ρ) (hα : 1 / 2 < α) :
    (∫ r in Ioi ρ,
      (2 * α * (ρ ^ 2 / r ^ 2) * (1 - ρ ^ 2 / r ^ 2) ^ (α - 1)) ^ 2 / r) =
      α / (2 * α - 1) := by
  let g : ℝ → ℝ := fun u => 2 * α ^ 2 * (u * (1 - u) ^ (2 * α - 2))
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r (hr : r ∈ Ioi ρ) =>
      (hasDerivAt_radius_substitution (ne_of_gt (hρ.trans hr))).hasDerivWithinAt)
    (radius_substitution_injective hρ) g
  rw [radius_substitution_image hρ] at hchange
  have hscalar : (∫ u in Ioo 0 1, g u) = α / (2 * α - 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    dsimp [g]
    rw [intervalIntegral.integral_const_mul]
    exact square_function_constant hα
  rw [← hscalar, hchange]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change ρ < r at hr
  have hrpos : 0 < r := hρ.trans hr
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hb : 0 < 1 - ρ ^ 2 / r ^ 2 := by
    have : ρ ^ 2 / r ^ 2 < 1 :=
      (div_lt_one (sq_pos_of_pos hrpos)).2 (by nlinarith)
    linarith
  have hp : ((1 - ρ ^ 2 / r ^ 2) ^ (α - 1)) ^ (2 : ℕ) =
      (1 - ρ ^ 2 / r ^ 2) ^ (2 * α - 2) := by
    rw [← Real.rpow_mul_natCast hb.le]
    congr 1
    ring
  have hneg : -2 * ρ ^ 2 / r ^ 3 < 0 := div_neg_of_neg_of_pos
    (by nlinarith [sq_pos_of_pos hρ]) (pow_pos hrpos 3)
  simp only [g, smul_eq_mul, abs_of_neg hneg]
  rw [mul_pow, hp]
  field_simp


/- The value on and outside the sphere is set to zero, as in the source's
   differentiated multiplier. The boundary value is irrelevant to integration. -/
noncomputable def radiusMultiplier (α ρ r : ℝ) : ℝ :=
  if ρ < r then 2 * α * (ρ ^ 2 / r ^ 2) * (1 - ρ ^ 2 / r ^ 2) ^ (α - 1)
  else 0

theorem measurable_radiusMultiplier (α : ℝ) :
    Measurable (fun x : ℝ × ℝ => radiusMultiplier α x.1 x.2) := by
  unfold radiusMultiplier
  apply Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
  · fun_prop
  · exact measurable_const

theorem radius_lintegral {ρ α : ℝ} (hρ : 0 < ρ) (hα : 1 / 2 < α) :
    (∫⁻ r in Ioi 0, ENNReal.ofReal ((radiusMultiplier α ρ r) ^ 2 / r)) =
      ENNReal.ofReal (α / (2 * α - 1)) := by
  let f : ℝ → ℝ := fun r =>
    (2 * α * (ρ ^ 2 / r ^ 2) * (1 - ρ ^ 2 / r ^ 2) ^ (α - 1)) ^ 2 / r
  have hi : IntegrableOn f (Ioi ρ) := by
    apply Integrable.of_integral_ne_zero
    rw [show (∫ r in Ioi ρ, f r) = α / (2 * α - 1) from radius_integral hρ hα]
    exact ne_of_gt (div_pos (by linarith) (by linarith))
  have hn : 0 ≤ᵐ[volume.restrict (Ioi ρ)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact div_nonneg (sq_nonneg _) (le_of_lt (hρ.trans hr))
  have he : (fun r => ENNReal.ofReal ((radiusMultiplier α ρ r) ^ 2 / r)) =
      (Ioi ρ).indicator (fun r => ENNReal.ofReal (f r)) := by
    ext r
    by_cases hr : ρ < r
    · simp [radiusMultiplier, hr, f]
    · simp [radiusMultiplier, hr]
  rw [he, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hρ.le)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, radius_integral hρ hα]

/-- Tonelli's theorem integrates the scalar identity against any spectral energy density. -/
theorem spectral_energy_identity {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {α : ℝ} (hα : 1 / 2 < α)
    (R : X → ℝ) (hR : Measurable R) (hpos : ∀ᵐ x ∂μ, 0 < R x)
    (F : X → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ r in Ioi 0, ∫⁻ x,
      ENNReal.ofReal ((radiusMultiplier α (R x) r) ^ 2 / r) * F x ∂μ) =
      ENNReal.ofReal (α / (2 * α - 1)) * ∫⁻ x, F x ∂μ := by
  have hm : Measurable (fun z : ℝ × X => radiusMultiplier α (R z.2) z.1) :=
    (measurable_radiusMultiplier α).comp ((hR.comp measurable_snd).prodMk measurable_fst)
  have he : Measurable (fun z : ℝ × X =>
      ENNReal.ofReal ((radiusMultiplier α (R z.2) z.1) ^ 2 / z.1)) := by
    fun_prop
  have hmeas : Measurable (fun z : ℝ × X =>
      ENNReal.ofReal ((radiusMultiplier α (R z.2) z.1) ^ 2 / z.1) * F z.2) :=
    he.mul (hF.comp measurable_snd)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (α / (2 * α - 1)) * F x ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpos] with x hx
      have hmx : Measurable (fun r : ℝ => radiusMultiplier α (R x) r) :=
        (measurable_radiusMultiplier α).comp (measurable_const.prodMk measurable_id)
      rw [lintegral_mul_const (F x) (by fun_prop), radius_lintegral hx hα]
    _ = _ := lintegral_const_mul _ hF

end OAI.Analysis.Fourier.SquareFunction
