import OAI.Geometry.Nikodym.FullStrip

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym

theorem setLIntegral_dilate {n : ℕ} {r : ℝ} (hr : r ≠ 0)
    {s : Set (Space n)} (hs : MeasurableSet s) {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x in s, F x) = ENNReal.ofReal (|r|^n) *
      ∫⁻ y in (fun y : Space n => r • y) ⁻¹' s, F (r • y) := by
  have h := setLIntegral_map hs hF (measurable_const_smul r)
    (μ:=(volume : Measure (Space n)))
  rw [Measure.map_addHaar_smul volume hr] at h
  simp only [Space,finrank_euclideanSpace_fin,abs_inv,abs_pow,Measure.restrict_smul,
    lintegral_smul_measure] at h
  have hrp : 0 < |r|^n := pow_pos (abs_pos.mpr hr) n
  rw [ENNReal.ofReal_inv_of_pos hrp] at h
  have hh := congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal (|r|^n)*t) h
  simp only [smul_eq_mul] at hh
  rw [← mul_assoc,ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hrp))
    ENNReal.ofReal_ne_top,one_mul] at hh
  exact hh

end OAI.Geometry.Nikodym
