import OAI.Analysis.Fourier.WavePackets.Tail

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal NNReal

/-- Hölder's inequality against the constant function, with no finiteness
assumption on the measure or integral. -/
theorem lintegral_rpow_le_mass_mul {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, f x ∂ν) ^ p ≤ ν Set.univ ^ (p - 1) * ∫⁻ x, f x ^ p ∂ν := by
  have hp₀ : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hi : 0 ≤ 1 / p := by positivity
  have hi₁ : 0 ≤ 1 - 1 / p := by
    have : 1 / p ≤ 1 := (div_le_one hp₀).mpr hp
    linarith
  have hhold := ENNReal.lintegral_mul_norm_pow_le
    (μ := ν) (f := fun x => f x ^ p) (g := fun _ => 1)
    (hf.pow_const p).aemeasurable measurable_const.aemeasurable
    hi hi₁ (by ring)
  simp only [← ENNReal.rpow_mul, mul_one_div_cancel hp₀.ne', ENNReal.rpow_one,
    ENNReal.one_rpow, mul_one, lintegral_const] at hhold
  have hpow := ENNReal.rpow_le_rpow hhold hp₀.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp₀.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hpow
  have hi_id : 1 / p * p = 1 := by field_simp
  have hi_id' : (1 - 1 / p) * p = p - 1 := by field_simp
  simpa only [hi_id, hi_id', ENNReal.rpow_one, one_mul, mul_comm] using hpow

/-- Weighted Hölder in a form suited to convolution. -/
theorem lintegral_weighted_rpow_le {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {k f : α → ℝ≥0∞} (hk : Measurable k) (hf : Measurable f)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, k x * f x ∂ν) ^ p ≤
      (∫⁻ x, k x ∂ν) ^ (p - 1) * ∫⁻ x, k x * f x ^ p ∂ν := by
  have hb := lintegral_rpow_le_mass_mul (ν := ν.withDensity k) hf hp
  simpa only [lintegral_withDensity_eq_lintegral_mul _ hk hf,
    lintegral_withDensity_eq_lintegral_mul _ hk (hf.pow_const p),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Pi.mul_apply] using hb

section Convolution

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]

/-- Young's inequality for the nonnegative convolution, before taking the
`p`-th root. It allows infinite integrals. -/
theorem lintegral_convolution_rpow_le {k f : G → ℝ≥0∞}
    (hk : Measurable k) (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, (∫⁻ y, k y * f (x - y) ∂μ) ^ p ∂μ) ≤
      (∫⁻ y, k y ∂μ) ^ p * ∫⁻ x, f x ^ p ∂μ := by
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, k y ∂μ) ^ (p - 1) *
        (∫⁻ y, k y * f (x - y) ^ p ∂μ) ∂μ := by
      apply lintegral_mono
      intro x
      exact lintegral_weighted_rpow_le hk (hf.comp (measurable_const.sub measurable_id)) hp
    _ = (∫⁻ y, k y ∂μ) ^ (p - 1) *
        (∫⁻ x, ∫⁻ y, k y * f (x - y) ^ p ∂μ ∂μ) := by
      apply lintegral_const_mul''
      fun_prop
    _ = (∫⁻ y, k y ∂μ) ^ (p - 1) *
        (∫⁻ y, ∫⁻ x, k y * f (x - y) ^ p ∂μ ∂μ) := by
      rw [lintegral_lintegral_swap (by fun_prop)]
    _ = (∫⁻ y, k y ∂μ) ^ (p - 1) *
        ((∫⁻ y, k y ∂μ) * ∫⁻ x, f x ^ p ∂μ) := by
      congr 1
      have hid (y : G) : (∫⁻ x, k y * f (x - y) ^ p ∂μ) =
          k y * ∫⁻ x, f x ^ p ∂μ := by
        have hm : AEMeasurable (fun x : G => f (x - y) ^ p) μ := by fun_prop
        rw [lintegral_const_mul'' (k y) hm,
          lintegral_sub_right_eq_self (fun x => f x ^ p) y]
      simp_rw [hid]
      exact lintegral_mul_const'' _ hk.aemeasurable
    _ = _ := by
      rw [← mul_assoc]
      congr 1
      calc
        _ = (∫⁻ y, k y ∂μ) ^ (p - 1) * (∫⁻ y, k y ∂μ) ^ (1 : ℝ) := by
          rw [ENNReal.rpow_one]
        _ = (∫⁻ y, k y ∂μ) ^ (p - 1 + 1) :=
          (ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hp) zero_le_one).symm
        _ = _ := by congr 1; ring

/-- Complex convolution, written explicitly to expose the operator used by
the Euclidean transfer argument. -/
noncomputable def complexConvolution (k f : G → ℂ) (μ : Measure G) (x : G) : ℂ :=
  ∫ y, k y * f (x - y) ∂μ

theorem aestronglyMeasurable_complexConvolution {k f : G → ℂ}
    (hk : AEStronglyMeasurable k μ) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (complexConvolution k f μ) μ := by
  exact hk.convolution (ContinuousLinearMap.mul ℂ ℂ) hf

theorem complexConvolution_rpow_integral_le {k f : G → ℂ}
    (hk : Measurable k) (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, ‖complexConvolution k f μ x‖ₑ ^ p ∂μ) ≤
      (∫⁻ y, ‖k y‖ₑ ∂μ) ^ p * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  apply le_trans ?_ (lintegral_convolution_rpow_le hk.enorm hf.enorm hp)
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow ?_ (by linarith)
  simpa only [complexConvolution, enorm_mul] using
    enorm_integral_le_lintegral_enorm (fun y => k y * f (x - y))

/-- The finite-exponent `L¹ × Lᵖ → Lᵖ` Young inequality. -/
theorem eLpNorm_complexConvolution_le_of_measurable {k f : G → ℂ}
    (hk : Measurable k) (hf : Measurable f) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    eLpNorm (complexConvolution k f μ) p μ ≤ eLpNorm k 1 μ * eLpNorm f p μ := by
  have hp₀ : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
  have hpr₀ : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top
    (aestronglyMeasurable_complexConvolution hk.aestronglyMeasurable hf.aestronglyMeasurable),
    eLpNorm_one_eq_lintegral_enorm hk.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top hf.aestronglyMeasurable]
  have hb := ENNReal.rpow_le_rpow (complexConvolution_rpow_integral_le (μ := μ) hk hf hpr)
    (show 0 ≤ 1 / p.toReal by positivity)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / p.toReal by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hpr₀.ne', ENNReal.rpow_one] using hb

/-- Young's inequality for a.e.-strongly-measurable inputs. -/
theorem eLpNorm_complexConvolution_le {k f : G → ℂ}
    (hk : AEStronglyMeasurable k μ) (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    eLpNorm (complexConvolution k f μ) p μ ≤ eLpNorm k 1 μ * eLpNorm f p μ := by
  have heq : complexConvolution k f μ = complexConvolution (hk.mk k) (hf.mk f) μ :=
    convolution_congr (ContinuousLinearMap.mul ℂ ℂ) hk.ae_eq_mk hf.ae_eq_mk
  rw [heq, eLpNorm_congr_ae hk.ae_eq_mk, eLpNorm_congr_ae hf.ae_eq_mk]
  exact eLpNorm_complexConvolution_le_of_measurable hk.stronglyMeasurable_mk.measurable
    hf.stronglyMeasurable_mk.measurable hp hp_top

theorem memLp_complexConvolution {k f : G → ℂ}
    (hk : Integrable k μ) {p : ℝ≥0∞} (hf : MemLp f p μ)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    MemLp (complexConvolution k f μ) p μ := by
  exact (eLpNorm_complexConvolution_le hk.aestronglyMeasurable hf.aestronglyMeasurable hp hp_top).trans_lt
    (ENNReal.mul_lt_top (memLp_one_iff_integrable.mpr hk) hf.eLpNorm_lt_top)

/-- For `L¹` and finite `Lᵖ` input the defining convolution integral really
exists almost everywhere; the norm estimate is not using a default value
for nonintegrable Bochner integrals. -/
theorem complexConvolution_integrable_ae_of_measurable {k f : G → ℂ}
    (hkm : Measurable k) (hfm : Measurable f)
    (hk : Integrable k μ) {p : ℝ≥0∞} (hf : MemLp f p μ)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    ∀ᵐ x ∂μ, Integrable (fun y => k y * f (x - y)) μ := by
  have hp₀ : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
  have hpr₀ : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpr
  let F : G → ℝ≥0∞ := fun x => ∫⁻ y, ‖k y‖ₑ * ‖f (x - y)‖ₑ ∂μ
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hfinite : (∫⁻ x, F x ^ p.toReal ∂μ) < ∞ := by
    apply (lintegral_convolution_rpow_le hkm.enorm hfm.enorm hpr).trans_lt
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hpr₀.le
        (by simpa only [hasFiniteIntegral_iff_enorm] using hk.hasFiniteIntegral.ne))
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ hp_top hf)
  filter_upwards [ae_lt_top (hFm.pow_const p.toReal) hfinite.ne] with x hx
  refine ⟨(hkm.mul (hfm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [enorm_mul] using (ENNReal.rpow_lt_top_iff_of_pos hpr₀).mp hx

theorem complexConvolution_integrable_ae {k f : G → ℂ}
    (hk : Integrable k μ) {p : ℝ≥0∞} (hf : MemLp f p μ)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    ∀ᵐ x ∂μ, Integrable (fun y => k y * f (x - y)) μ := by
  let hkm := hk.aestronglyMeasurable
  let hfm := hf.aestronglyMeasurable
  have hki : Integrable (hkm.mk k) μ := hk.congr hkm.ae_eq_mk
  have hfi : MemLp (hfm.mk f) p μ := hf.ae_eq hfm.ae_eq_mk
  filter_upwards [complexConvolution_integrable_ae_of_measurable
    hkm.stronglyMeasurable_mk.measurable hfm.stronglyMeasurable_mk.measurable
    hki hfi hp hp_top] with x hx
  apply hx.congr
  filter_upwards [hkm.ae_eq_mk,
    hfm.ae_eq_mk.comp_tendsto
      (quasiMeasurePreserving_sub_left_of_right_invariant μ x).tendsto_ae] with y hy hz
  change f (x - y) = hfm.mk f (x - y) at hz
  simp only [hy, hz]

end Convolution

section WaveTail

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

theorem waveTail_convolution_integrable_ae {a : E → ℂ}
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) {T h : ℝ}
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    {f : E → ℂ} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∀ᵐ x ∂μ, Integrable (fun y => waveTail μ a h T y * f (x - y)) μ := by
  obtain ⟨C, hC, hb⟩ := waveTail_integrable_and_L1_bound (μ := μ) ha hzero hs 0
  exact complexConvolution_integrable_ae (hb T h hT₀ hT₁ hh hh₁).1 hf hp hp_top

/-- Uniform rapid-decay operator norm of the off-cone tail on every finite
`Lᵖ`, including the critical exponent used in the transfer argument. -/
theorem waveTail_convolution_eLpNorm_bound {a : E → ℂ}
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T h : ℝ), 0 ≤ T → T ≤ 2 → 0 < h → h ≤ 1 →
      ∀ (f : E → ℂ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → MemLp f p μ →
        MemLp (complexConvolution (waveTail μ a h T) f μ) p μ ∧
        eLpNorm (complexConvolution (waveTail μ a h T) f μ) p μ ≤
          ENNReal.ofReal (C * h ^ N) * eLpNorm f p μ := by
  obtain ⟨C, hC, hb⟩ := waveTail_integrable_and_L1_bound (μ := μ) ha hzero hs N
  refine ⟨C, hC, ?_⟩
  intro T h hT₀ hT₁ hh hh₁ f p hp hp_top hf
  obtain ⟨hint, hnorm⟩ := hb T h hT₀ hT₁ hh hh₁
  refine ⟨memLp_complexConvolution hint hf hp hp_top, ?_⟩
  apply (eLpNorm_complexConvolution_le hint.aestronglyMeasurable
    hf.aestronglyMeasurable hp hp_top).trans
  apply mul_le_mul' ?_ le_rfl
  have heq := (memLp_one_iff_integrable.mpr hint).eLpNorm_eq_integral_rpow_norm
    one_ne_zero ENNReal.one_ne_top
  simp only [ENNReal.toReal_one, Real.rpow_one, inv_one] at heq
  rw [heq]
  exact ENNReal.ofReal_le_ofReal hnorm

end WaveTail

end OAI.Analysis.Fourier.WavePackets
