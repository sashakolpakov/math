import OAI.MeasureTheory.Kakeya.DirectionIntegral
import OAI.MeasureTheory.Kakeya.Jensen

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem kakeya_subcritical_scale {n : ℕ} (hn : 1 ≤ n) {p q D U δ I : ℝ}
    (hpq : p.HolderConjugate q) (hD : 0 < D) (_hU : 0 < U) (hδ : 0 < δ) (hI : 0 ≤ I) :
    (U * (32 * δ) ^ (n - 1)) * ((4 : ℝ) ^ n) ^ p *
        ((D * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) *
          I ^ (1 / p)) ^ p) =
      (U * 32 ^ (n - 1) * ((4 : ℝ) ^ n) ^ p * D ^ p) * δ ^ (2 * p - 2 * n) * I := by
  have hpqdiv : p / q = p - 1 := by
    apply (div_eq_iff hpq.symm.pos.ne').mpr
    nlinarith [hpq.mul_eq_add]
  have hnat : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
  have he : (n - 1 : ℕ) +
      ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) * p = 2 * p - 2 * n := by
    calc
      _ = (n - 1 : ℕ) + (2 * (n : ℝ) + (n - 1 : ℕ)) * (p / q) -
          3 * (n - 1 : ℕ) * p := by ring
      _ = _ := by rw [hpqdiv, hnat]; ring
  have hpower : ((D * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) *
          I ^ (1 / p)) ^ p) = D ^ p *
      δ ^ (((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) * p) * I := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hD.le (by positivity), ← Real.rpow_mul hδ.le,
      ← Real.rpow_mul hI, one_div_mul_cancel hpq.pos.ne', Real.rpow_one]
  have hδpowers : δ ^ (n - 1) *
      δ ^ (((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) * p) =
      δ ^ (2 * p - 2 * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hδ, he]
  calc
    _ = (U * 32 ^ (n - 1) * ((4 : ℝ) ^ n) ^ p * D ^ p) *
        (δ ^ (n - 1) * δ ^ (((2 * (n : ℝ) + (n - 1 : ℕ)) / q -
          3 * (n - 1 : ℕ)) * p)) * I := by rw [hpower, mul_pow]; ring
    _ = _ := by rw [hδpowers]

/-- Spherical restriction gives the sharp subcritical Kakeya maximal
moment estimate, on the whole sphere and for all spatial tube centers. -/
theorem restriction_implies_subcritical_kakeya_moment
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hpn : p < n) :
    ∃ J : ℝ, 0 < J ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) volume →
      (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ p ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ENNReal.ofReal (J * δ ^ (2 * p - 2 * n) * ∫ y, ‖f y‖ ^ p) := by
  obtain ⟨D, hD, hdiscrete⟩ := restriction_implies_discrete_kakeya hR n hn hpq hpn
  obtain ⟨U, hU, hcap⟩ := packetCap_real_upper_all_scales (n := n) (by omega)
  refine ⟨U * 32 ^ (n - 1) * ((4 : ℝ) ^ n) ^ p * D ^ p, by positivity, ?_⟩
  intro δ hδ hδone f hf
  obtain ⟨m, v, hv, hsep, hcover⟩ := unit_sphere_finite_separated_net (n := n) hδ
  have hcapbound (i : Fin m) : OAI.Analysis.Fourier.Restriction.sphereMeasure n (packetCap (32 * δ) (v i)) ≤
      ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) := by
    calc
      _ = ENNReal.ofReal ((OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap (32 * δ) (v i))) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hcap (32 * δ) (v i) (by positivity) (hv i))
  have hsum := hdiscrete m δ hδ hδone v hv hsep f hf
  have hI : 0 ≤ ∫ y, ‖f y‖ ^ p := integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg _) _
  calc
    _ ≤ ∑ i, OAI.Analysis.Fourier.Restriction.sphereMeasure n (packetCap (32 * δ) (v i)) *
        (ENNReal.ofReal ((4 : ℝ) ^ n) * OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i)) ^ p :=
      lintegral_kakeya_le_net hδ hpq.pos.le f v hcover
    _ ≤ ∑ i, ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) *
        (ENNReal.ofReal ((4 : ℝ) ^ n) * OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i)) ^ p := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul' (hcapbound i) le_rfl
    _ = (ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) * ENNReal.ofReal ((4 : ℝ) ^ n) ^ p) *
        ∑ i, OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i) ^ p := by
      simp only [ENNReal.mul_rpow_of_nonneg _ _ hpq.pos.le, Finset.mul_sum, mul_assoc]
    _ ≤ (ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) * ENNReal.ofReal ((4 : ℝ) ^ n) ^ p) *
        ENNReal.ofReal ((D * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q -
          3 * (n - 1 : ℕ)) * (∫ y, ‖f y‖ ^ p) ^ (1 / p)) ^ p) :=
      mul_le_mul' le_rfl hsum
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hpq.pos.le,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact kakeya_subcritical_scale (by omega) hpq hD hU hδ hI

theorem restriction_implies_critical_kakeya_moment
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℝ, 0 < J ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : Space n → ℂ, MemLp f n volume →
      (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ (n : ℝ) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ENNReal.ofReal (J * δ ^ (-ε * n) * ∫ y, ‖f y‖ ^ (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let p : ℝ := max (((n : ℝ) + 1) / 2) ((n : ℝ) - ε * n / 2)
  have hp1 : 1 < p := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hp : 0 < p := by linarith
  have hpn : p < n := max_lt (by linarith) (by nlinarith)
  have hpexp : -ε * n ≤ 2 * p - 2 * n := by
    have h := le_max_right (((n : ℝ) + 1) / 2) ((n : ℝ) - ε * n / 2)
    change (n : ℝ) - ε * n / 2 ≤ p at h
    linarith
  obtain ⟨J, hJ, hbound⟩ := restriction_implies_subcritical_kakeya_moment hR n hn
    (Real.HolderConjugate.conjExponent hp1) hpn
  refine ⟨J, hJ, ?_⟩
  intro δ hδ hδone f hf
  have hr : 1 ≤ (n : ℝ) / p := (le_div_iff₀ hp).mpr (by linarith)
  have hrpos : 0 < (n : ℝ) / p := by positivity
  have hpr : p * ((n : ℝ) / p) = n := by field_simp
  have hrp : ((n : ℝ) / p) * p = n := div_mul_cancel₀ _ hp.ne'
  have hfin : MemLp f (ENNReal.ofReal (p * ((n : ℝ) / p))) volume := by
    simpa only [hpr, ENNReal.ofReal_natCast] using hf
  have hg := memLp_kakeyaPowerInput hp hrpos hfin
  have hmoment := hbound δ hδ hδone (kakeyaPowerInput ((n : ℝ) / p) f) hg
  have heq : (fun y ↦ ‖kakeyaPowerInput ((n : ℝ) / p) f y‖ ^ p) =
      fun y ↦ ‖f y‖ ^ (n : ℝ) := by
    funext y
    rw [norm_kakeyaPowerInput, ← Real.rpow_mul (norm_nonneg _), hrp]
  rw [heq] at hmoment
  calc
    _ ≤ ∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (kakeyaPowerInput ((n : ℝ) / p) f) ω ^ p ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      apply lintegral_mono
      intro ω
      calc
        _ = (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ ((n : ℝ) / p)) ^ p := by
          rw [← ENNReal.rpow_mul, hrp]
        _ ≤ _ := ENNReal.rpow_le_rpow
          (kakeyaMaximal_rpow_le_powerInput hδ hr hf.aestronglyMeasurable ω) hp.le
    _ ≤ ENNReal.ofReal (J * δ ^ (2 * p - 2 * n) * ∫ y, ‖f y‖ ^ (n : ℝ)) := hmoment
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg _) _)
      apply mul_le_mul_of_nonneg_left _ hJ.le
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδone hpexp

theorem kakeya_moment_implies_norm_bound {n : ℕ} (hn : 1 ≤ n)
    {δ ε J : ℝ} (hδ : 0 < δ) (hJ : 0 < J)
    {f : Space n → ℂ} (hf : MemLp f n volume)
    (hmoment : (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ (n : ℝ) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (J * δ ^ (-ε * n) * ∫ y, ‖f y‖ ^ (n : ℝ))) :
    MemLp (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ∧
      eLpNorm (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ENNReal.ofReal (J ^ (1 / (n : ℝ)) * δ ^ (-ε)) * eLpNorm f n volume := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hnR.ne'
  have hI : 0 ≤ ∫ y, ‖f y‖ ^ (n : ℝ) :=
    integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hm : AEStronglyMeasurable (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    (measurable_kakeyaMaximal δ f hf.aestronglyMeasurable).aestronglyMeasurable
  have hfnorm : ENNReal.ofReal ((∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ))) =
      eLpNorm f n volume := by
    rw [← ofReal_lpNorm hf, lpNorm_eq_integral_norm_rpow_toReal hn0 (by simp)
      hf.aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, one_div]
  have hroot : (J * δ ^ (-ε * n) * ∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ)) =
      (J ^ (1 / (n : ℝ)) * δ ^ (-ε)) *
        (∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
    have he : (-ε * n) * (1 / (n : ℝ)) = -ε := by field_simp
    rw [Real.mul_rpow (by positivity) hI, Real.mul_rpow hJ.le (by positivity),
      ← Real.rpow_mul hδ.le, he]
  have hnorm : eLpNorm (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (J ^ (1 / (n : ℝ)) * δ ^ (-ε)) * eLpNorm f n volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hn0 (by simp) hm]
    simp only [ENNReal.toReal_natCast, enorm_eq_self]
    have h := ENNReal.rpow_le_rpow hmoment (by positivity : 0 ≤ 1 / (n : ℝ))
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), hroot,
      ENNReal.ofReal_mul (by positivity), hfnorm] at h
    exact h
  refine ⟨?_, hnorm⟩
  exact hnorm.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

/-- The full spherical restriction conjecture implies the Kakeya maximal
conjecture, with every strictly positive loss and the exact tube operator. -/
theorem restriction_implies_kakeyaMaximal
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture := by
  intro n hn ε hε
  obtain ⟨J, hJ, hmoment⟩ := restriction_implies_critical_kakeya_moment hR n hn hε
  refine ⟨J ^ (1 / (n : ℝ)), by positivity, ?_⟩
  intro δ hδ hδone f hf
  exact kakeya_moment_implies_norm_bound (by omega) hδ hJ hf (hmoment δ hδ hδone f hf)

end OAI.MeasureTheory.Kakeya
