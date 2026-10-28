import Mathlib

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set _root_.MeasureTheory
open scoped ENNReal

theorem rpow_lower_on_interval {A s : ℝ} (hA : 0 < A)
    (hs : A ≤ s) (hs' : s ≤ 2*A) (q : ℝ) :
    min (A^q) ((2*A)^q) ≤ s^q := by
  by_cases hq : 0 ≤ q
  · exact (min_le_left _ _).trans (Real.rpow_le_rpow hA.le hs hq)
  · exact (min_le_right _ _).trans
      (Real.rpow_le_rpow_of_nonpos (hA.trans_le hs) hs' (le_of_not_ge hq))

theorem lintegral_rpow_focal_interval {A N : ℝ} (hA : 0 < A) (hN : 0 < N) (q : ℝ) :
    ENNReal.ofReal (A*min (A^q) ((2*A)^q)*N^(-q-1)) ≤
      ∫⁻ t in Icc (A/N) (2*A/N), ENNReal.ofReal (t^q) := by
  let c := min (A^q) ((2*A)^q)
  have hc : 0 < c := lt_min (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos (by positivity) _)
  have he : A*c*N^(-q-1) = (c*N^(-q))*(2*A/N-A/N) := by
    rw [Real.rpow_sub hN,Real.rpow_one]
    ring
  rw [he,ENNReal.ofReal_mul (by positivity)]
  rw [←Real.volume_Icc,←Measure.restrict_apply_univ,←lintegral_const]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have ht0 : 0 < t := (div_pos hA hN).trans_le ht.1
  have hAt : A ≤ N*t := by nlinarith [(div_le_iff₀ hN).mp ht.1]
  have htA : N*t ≤ 2*A := by nlinarith [(le_div_iff₀ hN).mp ht.2]
  have hm := rpow_lower_on_interval hA hAt htA q
  rw [Real.mul_rpow hN.le ht0.le] at hm
  have hm' := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hN.le (-q))
  have hcancel : N^(-q)*N^q = 1 := by rw [←Real.rpow_add hN]; simp
  apply ENNReal.ofReal_le_ofReal
  calc
    c*N^(-q) = N^(-q)*c := mul_comm _ _
    _ ≤ N^(-q)*(N^q*t^q) := hm'
    _ = t^q := by rw [←mul_assoc,hcancel,one_mul]

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
