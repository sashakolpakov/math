import OAI.Geometry.Nikodym.Jacobi.Projective
import OAI.Geometry.Nikodym.Beltrami.Metric

noncomputable section
namespace OAI.Geometry.Nikodym

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem beltramiDenominator_radial (κ ρ : ℝ) {e : E} (he : ‖e‖ = 1) :
    beltramiDenominator κ (ρ • e) = 1 + κ*ρ^2 := by
  simp [beltramiDenominator,norm_smul,he,Real.norm_eq_abs,sq_abs]

theorem beltramiMetric_radial_split (κ ρ a b : ℝ) {e u v : E}
    (he : ‖e‖ = 1) (hu : ⟪e,u⟫ = 0) (hv : ⟪e,v⟫ = 0)
    (hq : 1 + κ*ρ^2 ≠ 0) :
    beltramiMetric κ (ρ • e) (a • e + u) (b • e + v) =
      a*b / (1+κ*ρ^2)^2 + ⟪u,v⟫ / (1+κ*ρ^2) := by
  have hee : ⟪e,e⟫ = (1:ℝ) := by simp [he]
  have hue : ⟪u,e⟫ = 0 := by rw [real_inner_comm,hu]
  simp only [beltramiMetric,beltramiDenominator_radial κ ρ he,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    hee,hu,hv,hue,mul_one,mul_zero,add_zero,zero_add]
  field_simp
  ring

def jacobiRadialVector (κ t : ℝ) (e w : E) : E :=
  (t*⟪e,w⟫) • e + curvatureSin κ t • (w - ⟪e,w⟫ • e)

theorem jacobiRadialVector_inner (κ t : ℝ) {e : E} (he : ‖e‖ = 1) (w z : E) :
    ⟪jacobiRadialVector κ t e w,jacobiRadialVector κ t e z⟫ =
      t^2*⟪e,w⟫*⟪e,z⟫ + (curvatureSin κ t)^2*(⟪w,z⟫-⟪e,w⟫*⟪e,z⟫) := by
  have hee : ⟪e,e⟫ = (1:ℝ) := by simp [he]
  simp only [jacobiRadialVector,inner_add_left,inner_add_right,inner_sub_left,
    inner_sub_right,real_inner_smul_left,real_inner_smul_right,hee]
  rw [real_inner_comm w e]
  ring

def normalRadialMetric (κ r : ℝ) (e w z : E) : ℝ :=
  ⟪e,w⟫*⟪e,z⟫ + (curvatureSin κ r/r)^2 * (⟪w,z⟫-⟪e,w⟫*⟪e,z⟫)

def projectiveRadialDerivative (κ r : ℝ) (e w : E) : E :=
  ((1/(curvatureCos κ r)^2)*⟪e,w⟫) • e +
    (curvatureTan κ r/r) • (w - ⟪e,w⟫ • e)

/-- Exact identification of the Jacobi normal metric with the Beltrami
metric under the projective radial change of variable. -/
theorem beltramiMetric_projectiveRadialDerivative (κ r : ℝ) {e : E}
    (he : ‖e‖ = 1) (hr : r ≠ 0) (hc : curvatureCos κ r ≠ 0) (w z : E) :
    beltramiMetric κ (curvatureTan κ r • e)
      (projectiveRadialDerivative κ r e w) (projectiveRadialDerivative κ r e z) =
        normalRadialMetric κ r e w z := by
  have hee : ⟪e,e⟫ = (1:ℝ) := by simp [he]
  have hp (v : E) : ⟪e,(curvatureTan κ r/r) • (v - ⟪e,v⟫ • e)⟫ = 0 := by
    simp only [real_inner_smul_right,inner_sub_right,hee,mul_one,sub_self,mul_zero]
  have hq : 1 + κ*(curvatureTan κ r)^2 ≠ 0 := by
    rw [curvatureTan_denominator κ r hc]
    exact one_div_ne_zero (pow_ne_zero 2 hc)
  unfold projectiveRadialDerivative
  rw [beltramiMetric_radial_split κ _ _ _ he (hp w) (hp z) hq]
  simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_left,
    inner_sub_right,hee,mul_one]
  rw [curvatureTan_denominator κ r hc]
  unfold normalRadialMetric curvatureTan
  have hwe : ⟪w,e⟫ = ⟪e,w⟫ := real_inner_comm _ _
  rw [hwe]
  field_simp
  ring

end OAI.Geometry.Nikodym
