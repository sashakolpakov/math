import Mathlib

/-! Integrable inverse-square derivatives give a limit with an explicit
inverse-radius remainder. -/

open _root_.MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem integrable_inverseSquare {r : ℝ} (hr : 0 < r) (C : ℝ) :
    IntegrableOn (fun t : ℝ => C / t ^ 2) (Ioi r) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hr).const_mul C
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := hr.trans ht
  rw [Real.rpow_neg ht0.le, Real.rpow_two]
  rfl

theorem integral_inverseSquare {r : ℝ} (hr : 0 < r) (C : ℝ) :
    (∫ t in Ioi r, C / t ^ 2) = C / r := by
  have hd : ∀ t ∈ Ici r, HasDerivAt (fun s : ℝ => -C / s) (C / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := (hr.trans_le ht).ne'
    have H := (hasDerivAt_const t (-C)).div (hasDerivAt_id t) ht0
    change HasDerivAt (fun s : ℝ => -C / s) ((0 * t - -C * 1) / t ^ 2) t at H
    convert H using 1 ; ring
  have ht : Tendsto (fun t : ℝ => -C / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have H := integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrable_inverseSquare hr C) ht
  simpa only [zero_sub, neg_div, neg_neg] using H

theorem inverseSquare_derivative_limit {F d : ℝ → ℝ} {C : ℝ}
    (_ : 0 ≤ C) (hdc : ContinuousOn d (Ici 1))
    (hd : ∀ t, 1 ≤ t → HasDerivAt F (d t) t)
    (hb : ∀ t, 1 ≤ t → |d t| ≤ C / t ^ 2) :
    ∃ L : ℝ, Tendsto F atTop (𝓝 L) ∧ ∀ r, 1 ≤ r → |F r - L| ≤ C / r := by
  have hi : IntegrableOn d (Ioi 1) := by
    apply (integrable_inverseSquare (by norm_num : (0 : ℝ) < 1) C).mono'
      ((hdc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hb t ht.le
  have hlim : Tendsto F atTop (𝓝 (limUnder atTop F)) :=
    tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (fun t ht => hd t ht.le) hi
  refine ⟨limUnder atTop F, hlim, ?_⟩
  intro r hr
  have hir : IntegrableOn d (Ioi r) := hi.mono_set (Ioi_subset_Ioi hr)
  have he := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t (ht : t ∈ Ici r) => hd t (hr.trans ht)) hir hlim
  calc
    |F r - limUnder atTop F| = |∫ t in Ioi r, d t| := by rw [he, abs_sub_comm]
    _ ≤ ∫ t in Ioi r, |d t| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := volume.restrict (Ioi r)) d
    _ ≤ ∫ t in Ioi r, C / t ^ 2 := by
      apply integral_mono_ae hir.abs (integrable_inverseSquare (by linarith) C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hb t (hr.trans ht.le)
    _ = C / r := integral_inverseSquare (by linarith) C

end OAI.Analysis.Fourier.Radial
