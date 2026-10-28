import OAI.Analysis.PDE.Concentration.Smoothing

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current
open scoped ContDiff

noncomputable def smoothedSquare {d : ℕ} (h : ℝ) (f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) : ℝ :=
  ∫ y, OAI.Analysis.Calculus.Current.smoothingKernel d h (x - y) * ‖f y‖ ^ 2

theorem integrable_smoothed_norm {d : ℕ} {h : ℝ} (hh : 0 < h)
    {f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} (hf : Measurable f) {A : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ A) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    Integrable (fun y => OAI.Analysis.Calculus.Current.smoothingKernel d h (x - y) * ‖f y‖) := by
  apply ((OAI.Analysis.Calculus.Current.integrable_smoothingKernel d h hh.ne').comp_sub_left x).mul_bdd
    hf.norm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by simpa using hb y

theorem integrable_smoothed_square {d : ℕ} {h : ℝ} (hh : 0 < h)
    {f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} (hf : Measurable f) {A : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ A) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    Integrable (fun y => OAI.Analysis.Calculus.Current.smoothingKernel d h (x - y) * ‖f y‖ ^ 2) := by
  apply ((OAI.Analysis.Calculus.Current.integrable_smoothingKernel d h hh.ne').comp_sub_left x).mul_bdd
    (c := A ^ 2) (hf.norm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f y‖)] using
      pow_le_pow_left₀ (norm_nonneg _) (hb y) 2

theorem smoothedSquare_nonneg {d : ℕ} {h : ℝ} (hh : 0 < h)
    (f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) : 0 ≤ smoothedSquare h f x :=
  integral_nonneg fun _ => mul_nonneg (OAI.Analysis.Calculus.Current.smoothingKernel_pos d h hh _).le (sq_nonneg _)

/-- Spatially nearby centers see comparable regularized squared amplitudes. -/
theorem smoothedSquare_comparable {d : ℕ} {h : ℝ} (hh : 0 < h)
    {f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} (hf : Measurable f) {A : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ A) {x x' : OAI.Analysis.Calculus.Current.SpatialSpace d} (hxx' : ‖x - x'‖ ≤ h) :
    smoothedSquare h f x ≤ 3 ^ (d + 3) * smoothedSquare h f x' := by
  unfold smoothedSquare
  rw [← integral_const_mul]
  apply integral_mono (integrable_smoothed_square hh hf hb x)
    ((integrable_smoothed_square hh hf hb x').const_mul _)
  intro y
  have h := smoothingKernel_comparable hh (x := x - y) (y := x' - y)
    (by simpa only [sub_sub_sub_cancel_right] using hxx')
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h (sq_nonneg ‖f y‖)

/-- Actual convolution by a kernel with a smoothing-kernel majorant has the
pointwise quadratic recovery bound used in the concentration argument. -/
theorem convolution_sq_le_smoothedSquare {d : ℕ} {h : ℝ} (hh : 0 < h)
    {f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} (hf : Measurable f) {A : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ A) {K : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ y, ‖K y‖ ≤ C * OAI.Analysis.Calculus.Current.smoothingKernel d h y) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖∫ y, K (x - y) * f y‖ ^ 2 ≤ C ^ 2 * smoothedSquare h f x := by
  have hmass : ∫ y, OAI.Analysis.Calculus.Current.smoothingKernel d h (x - y) = 1 := by
    rw [integral_sub_left_eq_self, OAI.Analysis.Calculus.Current.integral_smoothingKernel d h hh]
  have hp := pointwise_recovery_of_probability_majorant hC
    (fun y => (OAI.Analysis.Calculus.Current.smoothingKernel_pos d h hh (x - y)).le)
    ((OAI.Analysis.Calculus.Current.integrable_smoothingKernel d h hh.ne').comp_sub_left x) hmass
    (integrable_smoothed_norm hh hf hb x) (integrable_smoothed_square hh hf hb x)
    (fun y => hK (x - y))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hp 2
  rw [mul_pow] at hs
  change _ ≤ C ^ 2 * Real.sqrt (smoothedSquare h f x) ^ 2 at hs
  rw [Real.sq_sqrt (smoothedSquare_nonneg hh f x)] at hs
  exact hs

/-- The inverse multiplier bound holds throughout an `h`-ball around the
observation point, precisely the step leading to a density lower bound. -/
theorem convolution_sq_le_nearby_smoothedSquare {d : ℕ} {h : ℝ} (hh : 0 < h)
    {f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} (hf : Measurable f) {A : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ A) {K : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ y, ‖K y‖ ≤ C * OAI.Analysis.Calculus.Current.smoothingKernel d h y)
    {x x' : OAI.Analysis.Calculus.Current.SpatialSpace d} (hxx' : ‖x - x'‖ ≤ h) :
    ‖∫ y, K (x - y) * f y‖ ^ 2 ≤
      C ^ 2 * 3 ^ (d + 3) * smoothedSquare h f x' := by
  have hm := mul_le_mul_of_nonneg_left
    (smoothedSquare_comparable hh hf hb hxx') (sq_nonneg C)
  exact (convolution_sq_le_smoothedSquare hh hf hb hC hK x).trans
    (by simpa only [mul_assoc] using hm)

end OAI.Analysis.PDE.Concentration
