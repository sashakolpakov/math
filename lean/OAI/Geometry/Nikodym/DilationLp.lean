import OAI.Geometry.Nikodym.StripMoment

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym

theorem eLpNorm_dilate_dimension {F : Type*} [TopologicalSpace F]
    [ContinuousENorm F] {n : ℕ} (hn : 0 < n) {f : Space n → F}
    (hf : AEStronglyMeasurable f volume) {r : ℝ} (hr : r ≠ 0) :
    eLpNorm (fun x => f (r • x)) n volume =
      (ENNReal.ofReal |r|)⁻¹ * eLpNorm f n volume := by
  have hfm : AEStronglyMeasurable f (Measure.map (fun x : Space n => r • x) volume) :=
    hf.mono_ac (Measure.quasiMeasurePreserving_smul (volume : Measure (Space n)) hr).absolutelyContinuous
  have h := (eLpNorm_map_measure (p:=(n:ℝ≥0∞)) (g:=f) hfm
    (show AEMeasurable (fun x : Space n => r • x) volume from
      (measurable_const_smul r).aemeasurable)).symm
  rw [Measure.map_addHaar_smul (volume : Measure (Space n)) hr] at h
  simp only [Space,finrank_euclideanSpace_fin,abs_inv,abs_pow] at h
  rw [eLpNorm_smul_measure_of_ne_zero (by positivity) _ _ _] at h
  simp only [Function.comp_def,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_natCast,smul_eq_mul] at h
  have hc : ENNReal.ofReal ((|r|^n)⁻¹) ^ (1/(n:ℝ)) = (ENNReal.ofReal |r|)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (pow_pos (abs_pos.mpr hr) n),
      ENNReal.ofReal_pow (abs_nonneg r),ENNReal.inv_rpow]
    congr 1
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    simp [hn.ne']
  simpa only [hc] using h

end OAI.Geometry.Nikodym
