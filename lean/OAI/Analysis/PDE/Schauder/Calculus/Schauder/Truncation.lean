import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Cutoff

/-! Globally smooth, even far-field Newtonian kernels and their odd derivatives. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped Topology RealInnerProductSpace
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem newtonianEntry_neg (m : ℕ) (v w y : E) : newtonianEntry m v w (-y) = newtonianEntry m v w y := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [newtonianEntry_formula m v w (neg_ne_zero.mpr hy), newtonianEntry_formula m v w hy]
    simp

def truncatedNewtonianEntry (m : ℕ) (v w : E) (r : ℝ) (y : E) : ℝ :=
  (1 - radialCutoff r y) * newtonianEntry m v w y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_zero (m : ℕ) (v w : E) {r : ℝ} (hr : 0 < r)
    {y : E} (hy : ‖y‖ ≤ r) : truncatedNewtonianEntry m v w r y = 0 := by
  simp [truncatedNewtonianEntry, radialCutoff_one hr hy]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_eventually_zero (m : ℕ) (v w : E) {r : ℝ} (hr : 0 < r)
    {y : E} (hy : ‖y‖ < r) : truncatedNewtonianEntry m v w r =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
  exact truncatedNewtonianEntry_zero m v w hr hz.le

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_truncatedNewtonianEntry (m : ℕ) (v w : E) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (truncatedNewtonianEntry m v w r) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst y
    exact contDiffAt_const.congr_of_eventuallyEq
      (truncatedNewtonianEntry_eventually_zero m v w hr (by simpa using hr))
  · exact (contDiffAt_const.sub (contDiff_radialCutoff r).contDiffAt).mul
      ((contDiffAt_newtonianEntry m v w hy).of_le le_top)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_neg (m : ℕ) (v w y : E) (r : ℝ) :
    truncatedNewtonianEntry m v w r (-y) = truncatedNewtonianEntry m v w r y := by
  simp only [truncatedNewtonianEntry, radialCutoff_neg, newtonianEntry_neg]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_fderiv_neg (m : ℕ) (v w y : E) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (truncatedNewtonianEntry m v w r) (-y) =
      -fderiv ℝ (truncatedNewtonianEntry m v w r) y := by
  have hdiff := (contDiff_truncatedNewtonianEntry m v w hr).differentiable (by simp)
  have h := fderiv_reflect_translate (truncatedNewtonianEntry m v w r) hdiff 0 y
  have he : (fun z : E => truncatedNewtonianEntry m v w r (0 - z)) = truncatedNewtonianEntry m v w r := by
    funext z
    simp only [zero_sub, truncatedNewtonianEntry_neg]
  rw [he, zero_sub] at h
  exact (neg_eq_iff_eq_neg.mpr h).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_fderiv_zero (m : ℕ) (v w : E) {r : ℝ} (hr : 0 < r)
    {y : E} (hy : ‖y‖ < r) : fderiv ℝ (truncatedNewtonianEntry m v w r) y = 0 := by
  rw [(truncatedNewtonianEntry_eventually_zero m v w hr hy).fderiv_eq]
  simp

theorem truncatedNewtonianEntry_fderiv_integral_zero (m : ℕ) (v w u : E) {r : ℝ} (hr : 0 < r)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    (∫ y, fderiv ℝ (truncatedNewtonianEntry m v w r) y u ∂μ) = 0 := by
  have h := integral_neg_eq_self (fun y : E => fderiv ℝ (truncatedNewtonianEntry m v w r) y u) μ
  simp only [truncatedNewtonianEntry_fderiv_neg m v w _ hr, neg_apply, integral_neg] at h
  linarith

end OAI.Analysis.PDE.Schauder
