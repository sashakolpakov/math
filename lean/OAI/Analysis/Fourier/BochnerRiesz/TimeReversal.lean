import OAI.Analysis.Fourier.BochnerRiesz.PositiveTime

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff ComplexConjugate Topology

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem angularFourier_conj {n : ℕ} (f : Space n → ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ conj (f x)) ξ = conj (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (-ξ)) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [← Complex.exp_conj]

theorem angularInverse_conj {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ conj (g ξ)) x = conj (OAI.Analysis.Fourier.LocalSmoothing.angularInverse g (-x)) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  rw [← integral_conj]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp [← Complex.exp_conj]

theorem angularInverse_neg {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ g (-ξ)) x = OAI.Analysis.Fourier.LocalSmoothing.angularInverse g (-x) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  congr 1
  have h := integral_neg_eq_self (fun ξ : Space n ↦
    Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g (-ξ)) volume
  simpa only [neg_neg, inner_neg_right, inner_neg_left] using h.symm

theorem halfWaveIntegral_conj {n : ℕ} (f : Space n → ℂ) (t : ℝ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t (fun y ↦ conj (f y)) x = conj (OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (-t) f x) := by
  let g : Space n → ℂ := fun ξ ↦ Complex.exp (-Complex.I * ((-t) * ‖ξ‖ : ℝ)) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ
  have heq : (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
      OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun y ↦ conj (f y)) ξ) = (fun ξ ↦ conj (g (-ξ))) := by
    funext ξ
    rw [angularFourier_conj]
    simp [g, ← Complex.exp_conj]
  rw [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral, heq, angularInverse_conj, angularInverse_neg, neg_neg]
  rfl

def schwartzConj {n : ℕ} (f : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  f.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp] theorem schwartzConj_apply {n : ℕ} (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    schwartzConj f x = conj (f x) := rfl

theorem eLpNorm_schwartzConj {n : ℕ} (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (schwartzConj f) p volume = eLpNorm f p volume :=
  eLpNorm_conj (f : Space n → ℂ) p volume

def negativeTimeMeasure (n : ℕ) : Measure (Space n × ℝ) :=
  volume.prod (volume.restrict (Set.Iio 0))

theorem map_positive_time_neg :
    Measure.map (fun t : ℝ ↦ -t) (volume.restrict (Set.Ioi 0)) = volume.restrict (Set.Iio 0) := by
  have hpre : (fun t : ℝ ↦ -t) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by ext t; simp
  rw [← hpre, ← Measure.restrict_map measurable_neg measurableSet_Iio]
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)]

theorem map_positiveTimeMeasure_reflect (n : ℕ) :
    Measure.map (fun z : Space n × ℝ ↦ (z.1, -z.2)) (positiveTimeMeasure n) =
      negativeTimeMeasure n := by
  change Measure.map (Prod.map id (fun t : ℝ ↦ -t))
    (volume.prod (volume.restrict (Set.Ioi 0))) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_neg, Measure.map_id,
    map_positive_time_neg]
  rfl

theorem eLpNorm_time_reflect {n : ℕ} (F : Space n × ℝ → ℂ) (hF : Measurable F) (p : ℝ≥0∞) :
    eLpNorm (fun z : Space n × ℝ ↦ F (z.1, -z.2)) p (positiveTimeMeasure n) =
      eLpNorm F p (negativeTimeMeasure n) := by
  have hm : AEMeasurable (fun z : Space n × ℝ ↦ (z.1, -z.2)) (positiveTimeMeasure n) :=
    (by fun_prop : Measurable (fun z : Space n × ℝ ↦ (z.1, -z.2))).aemeasurable
  have H := (eLpNorm_map_measure (p := p) (g := F) hF.aestronglyMeasurable hm).symm
  rw [map_positiveTimeMeasure_reflect] at H
  exact H

theorem eLpNorm_weighted_schwartzConj {n : ℕ} (f : SchwartzMap (Space n) ℂ) (M : ℝ) (p : ℝ≥0∞) :
    eLpNorm (weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (schwartzConj f) z.1))
      p (positiveTimeMeasure n) =
    eLpNorm (weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
      p (negativeTimeMeasure n) := by
  have heq : weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (schwartzConj f) z.1) =
      conj (fun z : Space n × ℝ ↦ weightedTimeFunction M
        (fun q : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral q.2 f q.1) (z.1, -z.2)) := by
    funext z
    change (1 + |z.2|) ^ (-M) • OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (fun y ↦ conj (f y)) z.1 = _
    rw [halfWaveIntegral_conj]
    simp [weightedTimeFunction, Complex.real_smul]
  rw [heq, eLpNorm_conj, eLpNorm_time_reflect _
    (continuous_weightedTimeFunction M (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f)).measurable]

theorem localSmoothing_negative_weighted (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {p ε M : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hM : 1 / p + (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      eLpNorm (weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
        (ENNReal.ofReal p) (negativeTimeMeasure n) ≤
      ENNReal.ofReal (C * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hχ' : ContDiff ℝ ∞ (fun ξ : Space n ↦ χ (-ξ)) := hχ.comp contDiff_neg
  have hc' : HasCompactSupport (fun ξ : Space n ↦ χ (-ξ)) := by
    simpa only [neg_one_smul] using hc.comp_smul (show (-1 : ℝ) ≠ 0 by norm_num)
  have hz' : (0 : Space n) ∉ tsupport (fun ξ : Space n ↦ χ (-ξ)) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    have H := (notMem_tsupport_iff_eventuallyEq.mp hzero).comp_tendsto
      (show Filter.Tendsto (fun ξ : Space n ↦ -ξ) (𝓝 0) (𝓝 0) by
        simpa only [neg_zero] using continuous_neg.tendsto (0 : Space n))
    exact H
  obtain ⟨C, hC, hb⟩ := localSmoothing_positive_weighted hls hn hχ' hc' hz' hp hε hM
  refine ⟨C, hC, ?_⟩
  intro h hh hone f hcut
  have hcut' : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier (schwartzConj f) ξ ≠ 0 → χ (-(h • ξ)) = 1 := by
    intro ξ hξ
    have hfξ : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (-ξ) ≠ 0 := by
      intro hz
      apply hξ
      change OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ conj (f x)) ξ = 0
      rw [angularFourier_conj, hz, map_zero]
    simpa only [smul_neg] using hcut (-ξ) hfξ
  have H := hb h hh hone (schwartzConj f) hcut'
  rwa [eLpNorm_weighted_schwartzConj, eLpNorm_schwartzConj] at H

end OAI.Analysis.Fourier.BochnerRiesz
