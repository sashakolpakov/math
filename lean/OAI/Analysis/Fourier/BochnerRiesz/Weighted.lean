import OAI.Analysis.Fourier.BochnerRiesz.LocalSmoothing
import OAI.Analysis.Fourier.BochnerRiesz.Product

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def weightedTimeFunction {n : ℕ} (M : ℝ) (F : Space n × ℝ → ℂ) (z : Space n × ℝ) : ℂ :=
  (1 + |z.2|) ^ (-M) • F z

theorem continuous_weightedTimeFunction {n : ℕ} (M : ℝ) {F : Space n × ℝ → ℂ}
    (hF : Continuous F) : Continuous (weightedTimeFunction M F) := by
  unfold weightedTimeFunction
  change Continuous ((fun z : Space n × ℝ ↦ (1 + |z.2|) ^ (-M)) • F)
  apply Continuous.smul _ hF
  apply Continuous.rpow_const (by fun_prop)
  intro z
  exact Or.inl (by positivity)

theorem weightedTimeFunction_slab_bound {n : ℕ} (F : Space n × ℝ → ℂ) (hF : Continuous F)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r) (p : ℝ≥0∞) :
    eLpNorm (weightedTimeFunction M F) p (timeSlabMeasure n r) ≤
      ENNReal.ofReal ((1 + r) ^ (-M)) * eLpNorm F p (timeSlabMeasure n r) := by
  have hmem : ∀ᵐ z : Space n × ℝ ∂timeSlabMeasure n r, z.2 ∈ Set.Icc r (2 * r) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
    exact Filter.Eventually.of_forall fun _ ↦ ae_restrict_mem measurableSet_Icc
  have hcomp : eLpNorm (weightedTimeFunction M F) p (timeSlabMeasure n r) ≤
      eLpNorm (((1 + r) ^ (-M)) • F) p (timeSlabMeasure n r) := by
    apply eLpNorm_mono_ae (continuous_weightedTimeFunction M hF).aestronglyMeasurable
    filter_upwards [hmem] with z hz
    have hbase : 1 + r ≤ 1 + |z.2| := add_le_add le_rfl (hz.1.trans (le_abs_self _))
    have hb := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 1 + r) hbase (neg_nonpos.mpr hM)
    simp only [weightedTimeFunction, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + |z.2|) (-M)),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + r) (-M))]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  simpa only [eLpNorm_const_smul,
    Real.enorm_eq_ofReal (Real.rpow_nonneg (by linarith : 0 ≤ 1 + r) (-M))] using hcomp

theorem weighted_small_slab_bound {n : ℕ} {F : Space n × ℝ → ℂ} (hF : Continuous F)
    {M r q σ : ℝ} (hM : 0 ≤ M) (hr : 0 < r) (hrone : r ≤ 1) {p : ℝ≥0∞} {B : ℝ≥0∞}
    (hb : eLpNorm F p (timeSlabMeasure n r) ≤ ENNReal.ofReal (r ^ q * (max 1 r) ^ σ) * B) :
    eLpNorm (weightedTimeFunction M F) p (timeSlabMeasure n r) ≤ ENNReal.ofReal (r ^ q) * B := by
  have hw : ENNReal.ofReal ((1 + r) ^ (-M)) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hM)
  simp only [max_eq_left hrone, Real.one_rpow, mul_one] at hb
  exact (weightedTimeFunction_slab_bound F hF hM hr p).trans
    (by simpa only [one_mul] using mul_le_mul' hw hb)

theorem weighted_large_slab_bound {n : ℕ} {F : Space n × ℝ → ℂ} (hF : Continuous F)
    {M r q σ : ℝ} (hM : 0 ≤ M) (hrone : 1 ≤ r) {p : ℝ≥0∞} {B : ℝ≥0∞}
    (hb : eLpNorm F p (timeSlabMeasure n r) ≤ ENNReal.ofReal (r ^ q * (max 1 r) ^ σ) * B) :
    eLpNorm (weightedTimeFunction M F) p (timeSlabMeasure n r) ≤
      ENNReal.ofReal (r ^ (q + σ - M)) * B := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hrone
  have hw : ENNReal.ofReal ((1 + r) ^ (-M)) ≤ ENNReal.ofReal (r ^ (-M)) := by
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_nonpos hr (by linarith) (neg_nonpos.mpr hM)
  simp only [max_eq_right hrone, ← Real.rpow_add hr] at hb
  refine (weightedTimeFunction_slab_bound F hF hM hr p).trans ((mul_le_mul' hw hb).trans_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), ← Real.rpow_add hr]
  congr 3
  ring

theorem localSmoothing_all_positive_slabs (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ h r : ℝ, 0 < h → h ≤ 1 → 0 < r →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (timeSlabMeasure n r) ≤
      ENNReal.ofReal ((C * r ^ (1 / p) * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        (max 1 r) ^ (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA, ha⟩ := localSmoothing_annular_slab hls hn hχ hc hzero hp hε
  obtain ⟨B, hB, hb⟩ := shortTime_annular_slab hχ hc hzero (show 1 ≤ p by linarith)
  refine ⟨A + B + 1, by linarith, ?_⟩
  intro h r hh hone hr f hcut
  let σ := OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε
  have hσ : 0 ≤ σ := add_nonneg (le_max_left _ _) hε.le
  by_cases hhr : h ≤ r
  · refine (ha h r hh hhr f hcut).trans ?_
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    change A * r ^ (1 / p) * (h / r) ^ (-σ) ≤
      (A + B + 1) * r ^ (1 / p) * h ^ (-σ) * (max 1 r) ^ σ
    rw [Real.div_rpow hh.le hr.le, Real.rpow_neg hr.le, div_inv_eq_mul]
    calc
      _ = A * r ^ (1 / p) * h ^ (-σ) * r ^ σ := by ring
      _ ≤ _ := by gcongr; linarith; exact le_max_right 1 r
  · refine (hb h r hr (le_of_not_ge hhr) f hcut).trans ?_
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hrone : r ≤ 1 := (le_of_not_ge hhr).trans hone
    have hpow : 1 ≤ h ^ (-σ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh hone (neg_nonpos.mpr hσ)
    change B * r ^ (1 / p) ≤ (A + B + 1) * r ^ (1 / p) * h ^ (-σ) * (max 1 r) ^ σ
    rw [max_eq_left hrone, Real.one_rpow, mul_one]
    calc
      _ ≤ (A + B + 1) * r ^ (1 / p) := by gcongr; linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpow

end OAI.Analysis.Fourier.BochnerRiesz
