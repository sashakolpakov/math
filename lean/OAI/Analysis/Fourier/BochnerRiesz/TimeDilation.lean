import OAI.Analysis.Fourier.BochnerRiesz.Dilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def timeSlabMeasure (n : ℕ) (r : ℝ) : Measure (Space n × ℝ) :=
  volume.prod (volume.restrict (Set.Icc r (2 * r)))

theorem map_time_interval_dilate {r : ℝ} (hr : 0 < r) :
    Measure.map (fun t : ℝ ↦ r * t) (volume.restrict (Set.Icc 1 2)) =
      ENNReal.ofReal r⁻¹ • volume.restrict (Set.Icc r (2 * r)) := by
  have hpre : (fun t : ℝ ↦ r * t) ⁻¹' Set.Icc r (2 * r) = Set.Icc 1 2 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  rw [← hpre, ← Measure.restrict_map (by fun_prop) measurableSet_Icc]
  have hm : Measure.map (fun t : ℝ ↦ r * t) volume = ENNReal.ofReal r⁻¹ • volume := by
    simpa [smul_eq_mul, abs_of_pos (inv_pos.mpr hr)] using
      Measure.map_addHaar_smul (volume : Measure ℝ) hr.ne'
  rw [hm, Measure.restrict_smul]

theorem map_observation_dilate {n : ℕ} {r : ℝ} (hr : 0 < r) :
    Measure.map (fun z : Space n × ℝ ↦ (r • z.1, r * z.2)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) =
      ENNReal.ofReal ((r ^ (n + 1))⁻¹) • timeSlabMeasure n r := by
  change Measure.map (Prod.map (fun x : Space n ↦ r • x) (fun t : ℝ ↦ r * t))
    (volume.prod (volume.restrict (Set.Icc 1 2))) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), map_time_interval_dilate hr]
  rw [Measure.map_addHaar_smul (volume : Measure (Space n)) hr.ne']
  simp only [Space, finrank_euclideanSpace_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hr n))]
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hr.le n))]
  congr 1
  rw [pow_succ, mul_inv_rev]
  ring_nf

theorem eLpNorm_spacetime_dilate {n : ℕ} (F : Space n × ℝ → ℂ) (hF : Measurable F)
    (p : ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun z : Space n × ℝ ↦ F (r • z.1, r * z.2)) p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) =
      ENNReal.ofReal ((r ^ (n + 1))⁻¹) ^ (1 / p.toReal) *
        eLpNorm F p (timeSlabMeasure n r) := by
  have hm : AEMeasurable (fun z : Space n × ℝ ↦ (r • z.1, r * z.2))
      (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := (by fun_prop : Measurable
        (fun z : Space n × ℝ ↦ (r • z.1, r * z.2))).aemeasurable
  have h := (eLpNorm_map_measure (p := p) (g := F) hF.aestronglyMeasurable hm).symm
  rw [map_observation_dilate hr,
    eLpNorm_smul_measure_of_ne_zero (by positivity) _ _ _] at h
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul] using h

theorem spacetime_dilation_factor {n : ℕ} {r : ℝ} (hr : 0 < r) (q : ℝ) :
    ENNReal.ofReal ((r ^ (n + 1))⁻¹) ^ q * ENNReal.ofReal (r ^ q) =
      ENNReal.ofReal ((r ^ n)⁻¹) ^ q := by
  rw [ENNReal.ofReal_rpow_of_pos (inv_pos.mpr (pow_pos hr _)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)) _),
    ← Real.mul_rpow (inv_nonneg.mpr (pow_nonneg hr.le _)) hr.le]
  have hid : (r ^ (n + 1))⁻¹ * r = (r ^ n)⁻¹ := by
    rw [pow_succ, mul_inv_rev]
    field_simp
  rw [hid, ← ENNReal.ofReal_rpow_of_pos (inv_pos.mpr (pow_pos hr _))]

theorem map_spacetime_dilate {n : ℕ} {r : ℝ} (hr : 0 < r) :
    Measure.map (fun z : Space n × ℝ ↦ (r • z.1, r * z.2)) (volume.prod volume) =
      ENNReal.ofReal ((r ^ (n + 1))⁻¹) • (volume : Measure (Space n)).prod (volume : Measure ℝ) := by
  change Measure.map (Prod.map (fun x : Space n ↦ r • x) (fun t : ℝ ↦ r • t))
    (volume.prod volume) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_addHaar_smul (volume : Measure (Space n)) hr.ne',
    Measure.map_addHaar_smul (volume : Measure ℝ) hr.ne']
  simp only [Space, finrank_euclideanSpace_fin, Module.finrank_self, pow_one,
    abs_of_pos (inv_pos.mpr (pow_pos hr n)), abs_of_pos (inv_pos.mpr hr)]
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hr.le n))]
  congr 1
  rw [pow_succ, mul_inv_rev]
  ring_nf

theorem eLpNorm_spacetime_dilate_univ {n : ℕ} (F : Space n × ℝ → ℂ) (hF : Measurable F)
    (p : ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun z : Space n × ℝ ↦ F (r • z.1, r * z.2)) p (volume.prod volume) =
      ENNReal.ofReal ((r ^ (n + 1))⁻¹) ^ (1 / p.toReal) *
        eLpNorm F p (volume.prod volume) := by
  have hm : AEMeasurable (fun z : Space n × ℝ ↦ (r • z.1, r * z.2))
      (volume.prod volume) := (by fun_prop : Measurable
        (fun z : Space n × ℝ ↦ (r • z.1, r * z.2))).aemeasurable
  have H := (eLpNorm_map_measure (p := p) (g := F) hF.aestronglyMeasurable hm).symm
  rw [map_spacetime_dilate hr, eLpNorm_smul_measure_of_ne_zero (by positivity) _ _ _] at H
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul] using H

end OAI.Analysis.Fourier.BochnerRiesz
