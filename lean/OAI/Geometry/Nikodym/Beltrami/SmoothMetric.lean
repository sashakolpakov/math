import OAI.Geometry.Nikodym.Beltrami.Connection
import OAI.Geometry.Nikodym.SmoothMetric

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual bounded linear coefficient of the Beltrami metric. -/
def beltramiCoefficient (κ : ℝ) (x : E) : E →L[ℝ] E :=
  (beltramiDenominator κ x ^ 2)⁻¹ •
    (beltramiDenominator κ x • ContinuousLinearMap.id ℝ E -
      κ • (innerSL ℝ x).smulRight x)

omit [FiniteDimensional ℝ E] in
theorem inner_beltramiCoefficient (κ : ℝ) (x u v : E) :
    ⟪beltramiCoefficient κ x u,v⟫ = beltramiMetric κ x u v := by
  simp only [beltramiCoefficient,smul_apply,
    sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,inner_sub_left,
    real_inner_smul_left,beltramiMetric]
  ring

omit [FiniteDimensional ℝ E] in
theorem contDiffAt_beltramiCoefficient (κ : ℝ) {x : E}
    (hx : beltramiDenominator κ x ≠ 0) : ContDiffAt ℝ ∞ (beltramiCoefficient κ) x := by
  have hlin : ContDiff ℝ ∞ (fun y : E => innerSL ℝ y) :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).contDiff
  have hrank := hlin.smulRight (contDiff_id : ContDiff ℝ ∞ (fun y : E => y))
  have hkr : ContDiffAt ℝ ∞ (fun y : E => κ • (innerSL ℝ y).smulRight y) x := by
    simpa only using! ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => κ) x).smul hrank.contDiffAt)
  exact (((contDiff_beltramiDenominator κ).pow 2).contDiffAt.inv (pow_ne_zero 2 hx)).smul
    (((contDiff_beltramiDenominator κ).contDiffAt.smul contDiffAt_const).sub
      hkr)

omit [FiniteDimensional ℝ E] in
/-- Positivity holds throughout the full natural Beltrami domain. -/
theorem beltramiMetric_pos {κ : ℝ} {x u : E}
    (hx : 0 < beltramiDenominator κ x) (hu : u ≠ 0) :
    0 < beltramiMetric κ x u u := by
  have hnorm : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hcs : ⟪x,u⟫ ^ 2 ≤ ‖x‖ ^ 2 * ‖u‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) x u
    rw [Real.norm_eq_abs] at h
    have hh := (sq_le_sq₀ (abs_nonneg ⟪x,u⟫)
      (mul_nonneg (norm_nonneg x) (norm_nonneg u))).mpr h
    simpa only [sq_abs,mul_pow] using hh
  have hnum : 0 < beltramiDenominator κ x * ‖u‖^2 - κ * ⟪x,u⟫^2 := by
    by_cases hk : 0 ≤ κ
    · have hc := mul_le_mul_of_nonneg_left hcs hk
      dsimp [beltramiDenominator] at *
      nlinarith
    · have hc := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hk) (sq_nonneg ⟪x,u⟫)
      have hh := mul_pos hx hnorm
      linarith
  simpa only [beltramiMetric,real_inner_self_eq_norm_sq,pow_two,mul_assoc] using
    div_pos hnum (sq_pos_of_pos hx)

/-- The explicit model metric, now packaged as a genuine smooth positive
coordinate metric on its natural domain. -/
def beltramiSmoothMetric (κ : ℝ) : SmoothCoordinateMetric E where
  domain := {x | 0 < beltramiDenominator κ x}
  isOpen_domain := isOpen_lt continuous_const (contDiff_beltramiDenominator κ).continuous
  coefficient := beltramiCoefficient κ
  smooth := fun x hx => (contDiffAt_beltramiCoefficient κ hx.ne').contDiffWithinAt
  symmetric := by
    intro x hx u v
    have he : ⟪u,beltramiCoefficient κ x v⟫ = ⟪beltramiCoefficient κ x v,u⟫ := real_inner_comm _ _
    rw [he,inner_beltramiCoefficient,inner_beltramiCoefficient]
    exact beltramiMetric_symmetric κ x u v
  positive := by
    intro x hx u hu
    rw [inner_beltramiCoefficient]
    exact beltramiMetric_pos hx hu

omit [FiniteDimensional ℝ E] in
@[simp] theorem beltramiSmoothMetric_domain (κ : ℝ) :
    (beltramiSmoothMetric (E := E) κ).domain = {x | 0 < beltramiDenominator κ x} := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem beltramiSmoothMetric_inner (κ : ℝ) (x u v : E) :
    (beltramiSmoothMetric κ).inner x u v = beltramiMetric κ x u v :=
  inner_beltramiCoefficient κ x u v

end OAI.Geometry.Nikodym
