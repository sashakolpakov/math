import OAI.Analysis.Fourier.BochnerRiesz.Dilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem eLpNorm_dilate_vector {H : Type*} [NormedAddCommGroup H] {n : ℕ}
    (f : Space n → H) (hf : StronglyMeasurable f) (p : ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x ↦ f (r • x)) p (volume : Measure (Space n)) =
      ENNReal.ofReal ((r ^ n)⁻¹) ^ (1 / p.toReal) * eLpNorm f p (volume : Measure (Space n)) := by
  have hcont : Continuous (fun x : Space n ↦ r • x) := by fun_prop
  have hm : AEMeasurable (fun x : Space n ↦ r • x) (volume : Measure (Space n)) :=
    hcont.measurable.aemeasurable
  have h := (eLpNorm_map_measure (p := p) (g := f) hf.aestronglyMeasurable hm).symm
  rw [Measure.map_addHaar_smul (volume : Measure (Space n)) hr.ne'] at h
  simp only [Space, finrank_euclideanSpace_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hr n))] at h
  rw [eLpNorm_smul_measure_of_ne_zero (by positivity) _ _ _] at h
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul] using h

end OAI.Analysis.Fourier.BochnerRiesz
