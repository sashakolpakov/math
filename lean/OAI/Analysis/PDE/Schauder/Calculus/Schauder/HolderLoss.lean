import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PrincipalValue

/-! A nonsharp Hölder estimate for the compensated singular integral.
This intermediate estimate loses half the exponent; it does not assert the sharp Schauder bound.
-/

noncomputable section
open _root_.MeasureTheory Metric
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem holder_fourPoint (f : E → ℝ) {H α : ℝ} (hH : 0 ≤ H)
    (hf : ∀ a b, |f a - f b| ≤ H * ‖a - b‖ ^ α) (x z y : E) :
    |(f (x - y) - f x) - (f (z - y) - f z)| ≤
      2 * H * ‖x - z‖ ^ (α / 2) * ‖y‖ ^ (α / 2) := by
  by_cases hy : y = 0
  · subst y; simp; positivity
  by_cases hxz : x = z
  · subst z; simp; positivity
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hdpos : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hnear : |(f (x - y) - f x) - (f (z - y) - f z)| ≤ 2 * H * ‖y‖ ^ α := by
    have h1 := hf (x - y) x
    have h2 := hf (z - y) z
    have he (a : E) : ‖a - y - a‖ = ‖y‖ := by rw [sub_right_comm, sub_self, zero_sub, norm_neg]
    rw [he] at h1 h2
    exact (abs_sub _ _).trans (by linarith)
  have hfar : |(f (x - y) - f x) - (f (z - y) - f z)| ≤ 2 * H * ‖x - z‖ ^ α := by
    have h1 := hf (x - y) (z - y)
    have h2 := hf x z
    rw [sub_sub_sub_cancel_right] at h1
    have he : (f (x - y) - f x) - (f (z - y) - f z) =
        (f (x - y) - f (z - y)) - (f x - f z) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  have hm := mul_le_mul hfar hnear (abs_nonneg _) (by positivity : 0 ≤ 2 * H * ‖x - z‖ ^ α)
  have hy2 : (‖y‖ ^ (α / 2)) ^ 2 = ‖y‖ ^ α := by
    rw [pow_two, ← Real.rpow_add hypos]
    congr 1
    ring
  have hd2 : (‖x - z‖ ^ (α / 2)) ^ 2 = ‖x - z‖ ^ α := by
    rw [pow_two, ← Real.rpow_add hdpos]
    congr 1
    ring
  have hprod : 0 ≤ 2 * H * ‖x - z‖ ^ (α / 2) * ‖y‖ ^ (α / 2) := by positivity
  apply (sq_le_sq₀ (abs_nonneg _) hprod).mp
  rw [← hy2, ← hd2] at hm
  nlinarith only [hm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compensatedNewtonian_difference_bound (f : E → ℝ) {H α : ℝ} (hH : 0 ≤ H)
    (hf : ∀ a b, |f a - f b| ≤ H * ‖a - b‖ ^ α) (x z v w y : E) (hy : y ≠ 0) :
    ‖compensatedNewtonianEntry f x v w y - compensatedNewtonianEntry f z v w y‖ ≤
      (2 * H * newtonianSizeConstant (Module.finrank ℝ E) * ‖v‖ * ‖w‖ *
        ‖x - z‖ ^ (α / 2)) * ‖y‖ ^ (α / 2 - (Module.finrank ℝ E : ℝ)) := by
  have hfour := holder_fourPoint f hH hf x z y
  have hkernel := newtonianEntry_bound (Module.finrank ℝ E) hy v w
  rw [compensatedNewtonianEntry, compensatedNewtonianEntry, ← sub_mul, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (2 * H * ‖x - z‖ ^ (α / 2) * ‖y‖ ^ (α / 2)) *
        (newtonianSizeConstant (Module.finrank ℝ E) * ‖y‖ ^ (-(Module.finrank ℝ E : ℝ)) * ‖v‖ * ‖w‖) :=
      mul_le_mul hfour hkernel (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [show α / 2 - (Module.finrank ℝ E : ℝ) = α / 2 + -(Module.finrank ℝ E : ℝ) by ring,
        Real.rpow_add (norm_pos_iff.mpr hy)]
      ring

def localNewtonianSingular (f : E → ℝ) (R : ℝ) (v w x : E) : ℝ :=
  ∫ y in ball 0 R, compensatedNewtonianEntry f x v w y

theorem localNewtonianSingular_holderLoss (f : E → ℝ) (hfm : Measurable f)
    (hd : 1 ≤ Module.finrank ℝ E) {H α R : ℝ} (hH : 0 ≤ H) (hα : 0 < α) (hR : 0 < R)
    (hf : ∀ a b, |f a - f b| ≤ H * ‖a - b‖ ^ α) (v w x z : E) :
    |localNewtonianSingular f R v w x - localNewtonianSingular f R v w z| ≤
      (2 * H * newtonianSizeConstant (Module.finrank ℝ E) * ‖v‖ * ‖w‖ *
        rieszBallMass (volume : Measure E) (α / 2) * R ^ (α / 2)) * ‖x - z‖ ^ (α / 2) := by
  have hinc (a y : E) : |f (a - y) - f a| ≤ H * ‖y‖ ^ α := by
    have h := hf (a - y) a
    rw [show a - y - a = -y by abel, norm_neg] at h
    exact h
  have hIx := integrableOn_compensatedNewtonianEntry f x v w hd hfm hH hα (hinc x) volume R
  have hIz := integrableOn_compensatedNewtonianEntry f z v w hd hfm hH hα (hinc z) volume R
  let C := 2 * H * newtonianSizeConstant (Module.finrank ℝ E) * ‖v‖ * ‖w‖ * ‖x - z‖ ^ (α / 2)
  have hC : 0 ≤ C := by
    have := newtonianSizeConstant_nonneg (Module.finrank ℝ E)
    positivity
  have hmajor := (integrableOn_riesz_majorant (volume : Measure E) hd
    (show 0 < α / 2 by positivity) R).const_mul C
  have hbound : ∀ᵐ y ∂(volume : Measure E).restrict (ball 0 R),
      ‖compensatedNewtonianEntry f x v w y - compensatedNewtonianEntry f z v w y‖ ≤
        C * ‖y‖ ^ (α / 2 - (Module.finrank ℝ E : ℝ)) := by
    filter_upwards [] with y
    by_cases hy : y = 0
    · subst y
      simp only [compensatedNewtonianEntry, sub_zero, sub_self, zero_mul, norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (show 0 ≤ (0 : ℝ) by norm_num) _)
    · exact compensatedNewtonian_difference_bound f hH hf x z v w y hy
  have hi := norm_integral_le_of_norm_le hmajor hbound
  change |(∫ y in ball 0 R, compensatedNewtonianEntry f x v w y) -
    ∫ y in ball 0 R, compensatedNewtonianEntry f z v w y| ≤ _
  rw [← integral_sub hIx hIz]
  rw [integral_const_mul, integral_riesz_majorant_ball (volume : Measure E) (α / 2) hR] at hi
  rw [Real.norm_eq_abs] at hi
  convert hi using 1 ; dsimp [C] ; ring

end OAI.Analysis.PDE.Schauder
