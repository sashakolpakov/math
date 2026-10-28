import Mathlib

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set _root_.MeasureTheory
open scoped ENNReal

theorem lintegral_inv_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ t in Icc a b, ENNReal.ofReal (t⁻¹)) = ENNReal.ofReal (Real.log (b/a)) := by
  have hi : IntegrableOn (fun t : ℝ => t⁻¹) (Icc a b) :=
    (continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne')).integrableOn_compact isCompact_Icc
  rw [←ofReal_integral_eq_lintegral_ofReal hi]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab]
    exact integral_inv_of_pos ha (ha.trans_le hab)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact inv_nonneg.mpr (ha.le.trans ht.1)

theorem lintegral_inv_focusing_interval {A N : ℝ} (hA : 0 < A) (hN : 4*A ≤ N) :
    (∫⁻ t in Icc (A/N) (1/4:ℝ), ENNReal.ofReal (t⁻¹)) =
      ENNReal.ofReal (Real.log (N/(4*A))) := by
  have hN0 : 0 < N := (by positivity : 0 < 4*A).trans_le hN
  have hab : A/N ≤ (1/4:ℝ) := (div_le_iff₀ hN0).2 (by linarith)
  rw [lintegral_inv_Icc (div_pos hA hN0) hab]
  congr 2
  field_simp

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
