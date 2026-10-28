import OAI.Analysis.PDE.Concentration.Cylinder.Calculus

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set
open scoped ContDiff

noncomputable def cylinderTimeWeight (t : ℝ) : ℝ := Real.cos (t / 10)
noncomputable def cylinderTimeWeightDeriv (t : ℝ) : ℝ := -Real.sin (t / 10) / 10
noncomputable def cylinderTimeEnd : ℝ := 5 * Real.pi

theorem contDiff_cylinderTimeWeight : ContDiff ℝ ∞ cylinderTimeWeight :=
  Real.contDiff_cos.comp (contDiff_id.div_const 10)

theorem contDiff_cylinderTimeWeightDeriv : ContDiff ℝ ∞ cylinderTimeWeightDeriv :=
  ((Real.contDiff_sin.comp (contDiff_id.div_const 10)).neg).div_const 10

theorem hasDerivAt_cylinderTimeWeight (t : ℝ) :
    HasDerivAt cylinderTimeWeight (cylinderTimeWeightDeriv t) t := by
  convert ((Real.hasDerivAt_cos (t / 10)).comp t ((hasDerivAt_id t).div_const 10)) using 1
  · rfl
  · dsimp [cylinderTimeWeightDeriv]; ring

theorem hasDerivAt_cylinderTimeWeightDeriv (t : ℝ) :
    HasDerivAt cylinderTimeWeightDeriv (-cylinderTimeWeight t / 100) t := by
  convert (((Real.hasDerivAt_sin (t / 10)).comp t ((hasDerivAt_id t).div_const 10)).neg).div_const 10 using 1
  · rfl
  · dsimp [cylinderTimeWeight]; ring

theorem cylinderTimeWeight_end :
    cylinderTimeWeight cylinderTimeEnd = 0 ∧ cylinderTimeWeight (-cylinderTimeEnd) = 0 := by
  have h : cylinderTimeEnd / 10 = Real.pi / 2 := by dsimp [cylinderTimeEnd]; ring
  simp [cylinderTimeWeight, neg_div, h]

theorem cylinderTimeWeightDeriv_end :
    cylinderTimeWeightDeriv cylinderTimeEnd = -(1 / 10 : ℝ) ∧
      cylinderTimeWeightDeriv (-cylinderTimeEnd) = (1 / 10 : ℝ) := by
  have h : cylinderTimeEnd / 10 = Real.pi / 2 := by dsimp [cylinderTimeEnd]; ring
  simp [cylinderTimeWeightDeriv, neg_div, h]

theorem cylinderTimeWeight_nonneg {t : ℝ}
    (ht : t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd) : 0 ≤ cylinderTimeWeight t := by
  apply Real.cos_nonneg_of_mem_Icc
  dsimp [cylinderTimeEnd] at ht
  constructor <;> linarith [ht.1, ht.2]

/-- Exact integration by parts. Nonnegativity at the two time faces leaves
the desired favorable sign in the radial differential inequality. -/
theorem cylinderTimeWeight_second_deriv_integral {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    (∫ t in (-cylinderTimeEnd)..cylinderTimeEnd,
      cylinderTimeWeight t * deriv (deriv g) t) =
      (g cylinderTimeEnd + g (-cylinderTimeEnd)) / 10 -
        (∫ t in (-cylinderTimeEnd)..cylinderTimeEnd, cylinderTimeWeight t * g t) / 100 := by
  have hgd : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv (n := 1) |>.mp hg).2.2
  have hgdd : Continuous (deriv (deriv g)) :=
    (contDiff_succ_iff_deriv (n := 0) |>.mp hgd).2.2.continuous
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -cylinderTimeEnd) (b := cylinderTimeEnd)
    contDiff_cylinderTimeWeight.continuous.continuousOn hgd.continuous.continuousOn
    (fun t _ => hasDerivAt_cylinderTimeWeight t)
    (fun t _ => (hgd.differentiable (by norm_num) t).hasDerivAt)
    (contDiff_cylinderTimeWeightDeriv.continuous.intervalIntegrable _ _)
    (hgdd.intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -cylinderTimeEnd) (b := cylinderTimeEnd)
    contDiff_cylinderTimeWeightDeriv.continuous.continuousOn hg.continuous.continuousOn
    (fun t _ => hasDerivAt_cylinderTimeWeightDeriv t)
    (fun t _ => (hg.differentiable (by norm_num) t).hasDerivAt)
    (((contDiff_cylinderTimeWeight.continuous.neg).div_const 100).intervalIntegrable _ _)
    (hgd.continuous.intervalIntegrable _ _)
  rw [h1, h2, cylinderTimeWeight_end.1, cylinderTimeWeight_end.2,
    cylinderTimeWeightDeriv_end.1, cylinderTimeWeightDeriv_end.2]
  have he : (fun t => -cylinderTimeWeight t / 100 * g t) =
      (fun t => (-1 / 100 : ℝ) * (cylinderTimeWeight t * g t)) := by funext t; ring
  rw [he, intervalIntegral.integral_const_mul]
  ring

theorem cylinderTimeWeight_second_deriv_lower {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hleft : 0 ≤ g (-cylinderTimeEnd)) (hright : 0 ≤ g cylinderTimeEnd) :
    -(∫ t in (-cylinderTimeEnd)..cylinderTimeEnd, cylinderTimeWeight t * g t) / 100 ≤
      ∫ t in (-cylinderTimeEnd)..cylinderTimeEnd,
        cylinderTimeWeight t * deriv (deriv g) t := by
  rw [cylinderTimeWeight_second_deriv_integral hg]
  linarith

end OAI.Analysis.PDE.Concentration
