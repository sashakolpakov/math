import OAI.Analysis.Fourier.SquareFunction.Square.L2
import OAI.Analysis.Fourier.Wave.Multiplier

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.SquareFunction

open Set _root_.MeasureTheory
open scoped ENNReal

private theorem weighted_symbol_energy (m r : ℝ) (z : ℂ) (hr : 0 < r) :
    ENNReal.ofReal (m ^ 2 / r) * ENNReal.ofReal (‖z‖ ^ 2) =
      ENNReal.ofReal (‖(m : ℂ) * z‖ ^ 2 / r) := by
  rw [← ENNReal.ofReal_mul (div_nonneg (sq_nonneg m) hr.le)]
  congr 1
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem measurable_fourier_energy {n : ℕ} (α : ℝ) (f : OAI.Analysis.Fourier.Wave.WaveL2 n) :
    Measurable (fun z : ℝ × Space n =>
      ENNReal.ofReal ((radiusMultiplier α ‖z.2‖ z.1) ^ 2 / z.1) *
        ENNReal.ofReal (‖((Lp.fourierTransformₗᵢ (Space n) ℂ) f) z.2‖ ^ 2)) := by
  have hm : Measurable (fun z : ℝ × Space n => radiusMultiplier α ‖z.2‖ z.1) :=
    (measurable_radiusMultiplier α).comp ((continuous_norm.measurable.comp measurable_snd).prodMk
      measurable_fst)
  have hg := (Lp.stronglyMeasurable ((Lp.fourierTransformₗᵢ (Space n) ℂ) f)).measurable
  fun_prop

theorem measurable_radius_symbol {n : ℕ} (α r : ℝ) :
    Measurable (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ)) := by
  have hm : Measurable (fun ξ : Space n => radiusMultiplier α ‖ξ‖ r) :=
    (measurable_radiusMultiplier α).comp
    (continuous_norm.measurable.prodMk (measurable_const (a := r)))
  exact Complex.measurable_ofReal.comp hm

/-- Plancherel and Tonelli compute the entire radius-frequency energy. -/
theorem fourier_spectral_energy {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : OAI.Analysis.Fourier.Wave.WaveL2 n) :
    (∫⁻ r in Ioi 0, ∫⁻ ξ : Space n,
      ENNReal.ofReal ((radiusMultiplier α ‖ξ‖ r) ^ 2 / r) *
        ENNReal.ofReal (‖((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ‖ ^ 2)) =
      ENNReal.ofReal (α / (2 * α - 1) * ‖f‖ ^ 2) := by
  let g := (Lp.fourierTransformₗᵢ (Space n) ℂ) f
  have hpos : ∀ᵐ ξ : Space n ∂volume, 0 < ‖ξ‖ := by
    simp only [norm_pos_iff, ae_iff, not_not]
    exact measure_singleton (0 : Space n)
  have hF : Measurable (fun ξ : Space n => ENNReal.ofReal (‖g ξ‖ ^ 2)) := by
    have hg := (Lp.stronglyMeasurable g).measurable
    fun_prop
  rw [spectral_energy_identity volume hα (fun ξ : Space n => ‖ξ‖)
    continuous_norm.measurable hpos (fun ξ => ENNReal.ofReal (‖g ξ‖ ^ 2)) hF]
  have hi : Integrable (fun ξ => ‖g ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun ξ => sq_nonneg ‖g ξ‖)), ← OAI.Analysis.Fourier.Wave.waveL2_norm_sq_integral]
  dsimp [g]
  rw [LinearIsometryEquiv.norm_map,
    ← ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith))]

/-- The differentiated multiplier lies in its natural `L²` domain for almost every radius. -/
theorem ae_memLp_radius_symbol {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : OAI.Analysis.Fourier.Wave.WaveL2 n) :
    ∀ᵐ r ∂volume.restrict (Ioi 0),
      MemLp (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
        ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) 2 := by
  have hfinite := ae_lt_top (measurable_fourier_energy α f).lintegral_prod_right'
    (μ := volume.restrict (Ioi 0))
    (show (∫⁻ r in Ioi 0, ∫⁻ ξ : Space n,
      ENNReal.ofReal ((radiusMultiplier α ‖ξ‖ r) ^ 2 / r) *
        ENNReal.ofReal (‖((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ‖ ^ 2)) ≠ ∞ by
      rw [fourier_spectral_energy hα f]
      exact ENNReal.ofReal_ne_top)
  filter_upwards [hfinite, ae_restrict_mem measurableSet_Ioi] with r hfin hr
  change 0 < r at hr
  let g := (Lp.fourierTransformₗᵢ (Space n) ℂ) f
  have hm : AEStronglyMeasurable (fun ξ : Space n =>
      (radiusMultiplier α ‖ξ‖ r : ℂ) * g ξ) volume :=
    (measurable_radius_symbol α r).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)
  have hi : Integrable (fun ξ : Space n =>
      ‖(radiusMultiplier α ‖ξ‖ r : ℂ) * g ξ‖ ^ 2 / r) := by
    refine ⟨by simpa only [pow_two, div_eq_mul_inv, Pi.mul_apply] using
      (hm.norm.mul hm.norm).mul_const (r⁻¹),
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
        (fun ξ => div_nonneg (sq_nonneg _) hr.le))).2 ?_⟩
    simpa only [weighted_symbol_energy _ _ _ hr] using hfin
  apply (memLp_two_iff_integrable_sq_norm hm).2
  convert hi.mul_const r using 1
  ext ξ
  exact (div_mul_cancel₀ _ (ne_of_gt hr)).symm

/-- The differentiated Bochner--Riesz operator on its `L²` domain.
For arbitrary `L²` data, the exceptional radii outside this domain form a null set.
The value there is chosen to be zero. -/
noncomputable def differentiatedBochnerRieszL2 {n : ℕ} (α r : ℝ) (f : OAI.Analysis.Fourier.Wave.WaveL2 n) :
    OAI.Analysis.Fourier.Wave.WaveL2 n := by
  classical
  exact if h : MemLp (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
      ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) 2 then
    OAI.Analysis.Fourier.Wave.fourierMultiplierL2 (fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ)) f h else 0

theorem differentiatedBochnerRieszL2_energy {n : ℕ} (α r : ℝ)
    (hr : 0 < r) (f : OAI.Analysis.Fourier.Wave.WaveL2 n)
    (hdom : MemLp (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
      ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) 2) :
    ENNReal.ofReal (‖differentiatedBochnerRieszL2 α r f‖ ^ 2 / r) =
      ∫⁻ ξ : Space n, ENNReal.ofReal ((radiusMultiplier α ‖ξ‖ r) ^ 2 / r) *
        ENNReal.ofReal (‖((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ‖ ^ 2) := by
  have hi : Integrable (fun ξ : Space n =>
      ‖(radiusMultiplier α ‖ξ‖ r : ℂ) *
        ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hdom.aestronglyMeasurable).1 hdom
  have he : ‖differentiatedBochnerRieszL2 α r f‖ ^ 2 =
      ∫ ξ : Space n, ‖(radiusMultiplier α ‖ξ‖ r : ℂ) *
        ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ‖ ^ 2 := by
    rw [differentiatedBochnerRieszL2, dite_eq_left hdom,
      OAI.Analysis.Fourier.Wave.norm_sq_fourierMultiplierL2]
    simp only [norm_mul, mul_pow]
  rw [he, ← integral_div]
  rw [ofReal_integral_eq_lintegral_ofReal (hi.div_const r)
    (Filter.Eventually.of_forall (fun ξ => div_nonneg (sq_nonneg _) hr.le))]
  apply lintegral_congr
  intro ξ
  exact (weighted_symbol_energy _ _ _ hr).symm

/-- The exact `L²` Stein square-function identity, in integrated slice-norm form. -/
theorem stein_square_function_L2 {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : OAI.Analysis.Fourier.Wave.WaveL2 n) :
    (∫⁻ r in Ioi 0, ENNReal.ofReal (‖differentiatedBochnerRieszL2 α r f‖ ^ 2 / r)) =
      ENNReal.ofReal (α / (2 * α - 1) * ‖f‖ ^ 2) := by
  rw [← fourier_spectral_energy hα f]
  apply lintegral_congr_ae
  filter_upwards [ae_memLp_radius_symbol hα f, ae_restrict_mem measurableSet_Ioi]
    with r hr hpos
  exact differentiatedBochnerRieszL2_energy α r hpos f hr

theorem integrable_stein_energy {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : OAI.Analysis.Fourier.Wave.WaveL2 n) :
    IntegrableOn (fun r => ‖differentiatedBochnerRieszL2 α r f‖ ^ 2 / r) (Ioi 0) := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun r => ‖differentiatedBochnerRieszL2 α r f‖ ^ 2 / r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact div_nonneg (sq_nonneg _) hr.le
  have he : (fun r => ENNReal.ofReal (‖differentiatedBochnerRieszL2 α r f‖ ^ 2 / r))
      =ᵐ[volume.restrict (Ioi 0)] (fun r => ∫⁻ ξ : Space n,
        ENNReal.ofReal ((radiusMultiplier α ‖ξ‖ r) ^ 2 / r) *
          ENNReal.ofReal (‖((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ‖ ^ 2)) := by
    filter_upwards [ae_memLp_radius_symbol hα f, ae_restrict_mem measurableSet_Ioi]
      with r hr hpos
    exact differentiatedBochnerRieszL2_energy α r hpos f hr
  have hm : AEMeasurable (fun r => ENNReal.ofReal
      (‖differentiatedBochnerRieszL2 α r f‖ ^ 2 / r)) (volume.restrict (Ioi 0)) :=
    (measurable_fourier_energy α f).lintegral_prod_right'.aemeasurable.congr he.symm
  have hreal : AEStronglyMeasurable
      (fun r => ‖differentiatedBochnerRieszL2 α r f‖ ^ 2 / r)
      (volume.restrict (Ioi 0)) := by
    apply hm.ennreal_toReal.aestronglyMeasurable.congr
    filter_upwards [hn] with r hr
    exact ENNReal.toReal_ofReal hr
  refine ⟨hreal, (hasFiniteIntegral_iff_ofReal hn).2 ?_⟩
  rw [stein_square_function_L2 hα f]
  exact ENNReal.ofReal_lt_top

/-- Real-valued form of the exact square-function energy identity. -/
theorem stein_square_function_L2_real {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : OAI.Analysis.Fourier.Wave.WaveL2 n) :
    (∫ r in Ioi 0, ‖differentiatedBochnerRieszL2 α r f‖ ^ 2 / r) =
      α / (2 * α - 1) * ‖f‖ ^ 2 := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun r => ‖differentiatedBochnerRieszL2 α r f‖ ^ 2 / r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact div_nonneg (sq_nonneg _) hr.le
  have hc : 0 ≤ α / (2 * α - 1) * ‖f‖ ^ 2 :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have h := congrArg ENNReal.toReal (stein_square_function_L2 hα f)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_stein_energy hα f) hn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hn), ENNReal.toReal_ofReal hc] at h
  exact h

end OAI.Analysis.Fourier.SquareFunction
