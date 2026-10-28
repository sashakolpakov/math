import OAI.Analysis.Fourier.Estimates

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

instance sphereMeasure_isFinite (n : ℕ) : IsFiniteMeasure (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  unfold OAI.Analysis.Fourier.Restriction.sphereMeasure
  infer_instance

theorem norm_spherical_character {n : ℕ} (x ω : Space n) :
    ‖Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ))‖ = 1 := by
  simp [Complex.norm_exp]

theorem norm_spherical_integrand {n : ℕ} (g : Space n → ℂ) (x ω : Space n) :
    ‖Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω‖ = ‖g ω‖ := by
  rw [norm_mul, norm_spherical_character, one_mul]

theorem spherical_integrand_integrable {n : ℕ} {g : Space n → ℂ}
    (hg : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) (x : Space n) :
    Integrable (fun ω ↦ Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω)
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  apply hg.norm.mono'
  · have hchar : Continuous (fun ω : Space n ↦
        Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ))) := by fun_prop
    exact hchar.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact Eventually.of_forall fun ω ↦ (norm_spherical_integrand g x ω).le

/-- The elementary extension endpoint used for interpolation in the manuscript. -/
theorem norm_sphericalExtension_le {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖ ≤ ∫ ω, ‖g ω‖ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  unfold OAI.Analysis.Fourier.Restriction.sphericalExtension
  calc
    ‖∫ ω, Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n‖ ≤
      ∫ ω, ‖Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω‖ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
        norm_integral_le_integral_norm _
    _ = ∫ ω, ‖g ω‖ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by simp only [norm_spherical_integrand]

theorem continuous_sphericalExtension {n : ℕ} {g : Space n → ℂ}
    (hg : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) : Continuous (OAI.Analysis.Fourier.Restriction.sphericalExtension g) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (fun ω ↦ ‖g ω‖)
  · exact Eventually.of_forall fun z ↦ (spherical_integrand_integrable hg z).aestronglyMeasurable
  · exact Eventually.of_forall fun z ↦
      Eventually.of_forall fun ω ↦ (norm_spherical_integrand g z ω).le
  · exact hg.norm
  · exact Eventually.of_forall fun ω ↦ Continuous.tendsto (by fun_prop) x

theorem enorm_sphericalExtension_le {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖ₑ ≤ ∫⁻ ω, ‖g ω‖ₑ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  unfold OAI.Analysis.Fourier.Restriction.sphericalExtension
  calc
    ‖∫ ω, Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n‖ₑ ≤
      ∫⁻ ω, ‖Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω‖ₑ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ω, ‖g ω‖ₑ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      congr 1
      funext ω
      simp only [← ofReal_norm, norm_spherical_integrand]

theorem sphericalExtension_L1_Linfty {n : ℕ} {g : Space n → ℂ}
    (hg : MemLp g 1 (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) ∞ ∧
    eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) ∞ volume ≤ eLpNorm g 1 (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have hgi : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := memLp_one_iff_integrable.mp hg
  have hm := (continuous_sphericalExtension hgi).aestronglyMeasurable (μ := volume)
  have hb : eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) ∞ volume ≤ eLpNorm g 1 (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    rw [eLpNorm_exponent_top hm, eLpNorm_one_eq_lintegral_enorm hgi.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_enorm_bound
      (Eventually.of_forall (enorm_sphericalExtension_le g))
  exact ⟨hb.trans_lt hg, hb⟩

theorem sphericalExtension_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → Space n → ℂ) (hg : ∀ i ∈ s, Integrable (g i) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    (x : Space n) :
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ ∑ i ∈ s, g i ω) x = ∑ i ∈ s, OAI.Analysis.Fourier.Restriction.sphericalExtension (g i) x := by
  simp only [OAI.Analysis.Fourier.Restriction.sphericalExtension, Finset.mul_sum]
  exact integral_finsetSum s fun i hi ↦ spherical_integrand_integrable (hg i hi) x

theorem sphericalExtension_const_mul {n : ℕ} (c : ℂ) (g : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ c * g ω) x = c * OAI.Analysis.Fourier.Restriction.sphericalExtension g x := by
  unfold OAI.Analysis.Fourier.Restriction.sphericalExtension
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω ↦ by ring

/-- Convert an `Lp` operator bound to a bound on the corresponding power
integrals. Finiteness is explicit, so no `toReal` of infinity is used. -/
theorem integral_norm_rpow_le_of_eLpNorm_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → ℂ} {g : β → ℂ}
    {p q C : ℝ} (hp : 0 < p) (hq : 0 < q) (hC : 0 ≤ C)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal q) ν)
    (hbound : eLpNorm g (ENNReal.ofReal q) ν ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) μ) :
    (∫ y, ‖g y‖ ^ q ∂ν) ≤ C ^ q * (∫ x, ‖f x‖ ^ p ∂μ) ^ (q / p) := by
  have hr := (ENNReal.toReal_le_toReal hg.eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top)).mpr hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hr
  change lpNorm g (ENNReal.ofReal q) ν ≤ C * lpNorm f (ENNReal.ofReal p) μ at hr
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hpower := Real.rpow_le_rpow (lpNorm_nonneg (f := g)) hr hq.le
  rw [Real.mul_rpow hC lpNorm_nonneg] at hpower
  rw [lpNorm_eq_integral_norm_rpow_toReal hq0 ENNReal.ofReal_ne_top hg.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal hp0 ENNReal.ofReal_ne_top hf.aestronglyMeasurable] at hpower
  simp only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le] at hpower
  rw [← Real.rpow_mul (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    inv_mul_cancel₀ hq.ne', Real.rpow_one,
    ← Real.rpow_mul (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)] at hpower
  convert hpower using 1
  congr 2
  ring

/-- Small phase oscillation cannot cancel half the mass of a finite measure.
This is the analytic step in the packet lower bound of the Kakeya argument. -/
theorem small_phase_integral_lower_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (θ : α → ℝ) (hθ : Measurable θ)
    (hsmall : ∀ᵐ a ∂μ, |θ a| ≤ 1 / 4) :
    μ.real Set.univ / 2 ≤ ‖∫ a, Complex.exp (Complex.I * (θ a : ℂ)) ∂μ‖ := by
  have hn (a : α) : ‖Complex.exp (Complex.I * (θ a : ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  have hi : Integrable (fun a ↦ Complex.exp (Complex.I * (θ a : ℂ))) μ := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact ((Complex.measurable_ofReal.comp hθ).const_mul Complex.I).cexp.aestronglyMeasurable
    · exact Eventually.of_forall fun a ↦ (hn a).le
  have hre : ∀ᵐ a ∂μ, (1 / 2 : ℝ) ≤
      (Complex.exp (Complex.I * (θ a : ℂ))).re := by
    filter_upwards [hsmall] with a ha
    have habs := abs_le.mp ha
    have hcos := Real.one_sub_sq_div_two_le_cos (x := θ a)
    have hr : (Complex.exp (Complex.I * (θ a : ℂ))).re = Real.cos (θ a) := by
      simp [Complex.exp_re]
    rw [hr]
    nlinarith
  calc
    μ.real Set.univ / 2 = ∫ _ : α, (1 / 2 : ℝ) ∂μ := by
      simp [integral_const, smul_eq_mul, div_eq_mul_inv]
    _ ≤ ∫ a, (Complex.exp (Complex.I * (θ a : ℂ))).re ∂μ :=
      integral_mono_ae (integrable_const _) hi.re hre
    _ = (∫ a, Complex.exp (Complex.I * (θ a : ℂ)) ∂μ).re := integral_re hi
    _ ≤ ‖∫ a, Complex.exp (Complex.I * (θ a : ℂ)) ∂μ‖ := Complex.re_le_norm _

end OAI.Analysis.Fourier.Restriction
