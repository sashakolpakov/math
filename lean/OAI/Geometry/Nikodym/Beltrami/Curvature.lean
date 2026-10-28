import OAI.Geometry.Nikodym.Beltrami.Connection

noncomputable section
namespace OAI.Geometry.Nikodym

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def beltramiChristoffelVariation (κ : ℝ) (x u v w : E) : E :=
  (2*κ^2*⟪x,w⟫ / beltramiDenominator κ x ^ 2) • (⟪x,u⟫ • v + ⟪x,v⟫ • u) -
    (κ / beltramiDenominator κ x) • (⟪w,u⟫ • v + ⟪w,v⟫ • u)

theorem hasDerivAt_beltramiChristoffel {κ t : ℝ} {γ : ℝ → E} {w : E}
    (hγ : HasDerivAt γ w t) (hq : beltramiDenominator κ (γ t) ≠ 0) (u v : E) :
    HasDerivAt (fun s => beltramiChristoffel κ (γ s) u v)
      (beltramiChristoffelVariation κ (γ t) u v w) t := by
  have hdq := hasDerivAt_beltramiDenominator (κ := κ) hγ
  have hdu : HasDerivAt (fun s => ⟪γ s,u⟫) ⟪w,u⟫ t := by
    simpa using hγ.inner ℝ (hasDerivAt_const t u)
  have hdv : HasDerivAt (fun s => ⟪γ s,v⟫) ⟪w,v⟫ t := by
    simpa using hγ.inner ℝ (hasDerivAt_const t v)
  have hh := (((hasDerivAt_const t κ).div hdq hq).neg).smul
    ((hdu.smul_const v).add (hdv.smul_const u))
  convert hh using 1
  · rfl
  · simp only [beltramiChristoffelVariation,Pi.neg_apply,Pi.add_apply,Pi.mul_apply,Pi.inv_apply,
      sub_eq_add_neg,smul_add,smul_smul,div_eq_mul_inv]
    module

/-- Riemann curvature computed from the actual Christoffel derivative. -/
def beltramiCurvature (κ : ℝ) (x u v w : E) : E :=
  beltramiChristoffelVariation κ x v w u - beltramiChristoffelVariation κ x u w v +
    beltramiChristoffel κ x u (beltramiChristoffel κ x v w) -
    beltramiChristoffel κ x v (beltramiChristoffel κ x u w)

/-- The model really has constant curvature `κ`; the straightening result is
not based on a specially declared class of straight curves. -/
theorem beltramiCurvature_eq (κ : ℝ) (x u v w : E)
    (hq : beltramiDenominator κ x ≠ 0) :
    beltramiCurvature κ x u v w =
      κ • (beltramiMetric κ x v w • u - beltramiMetric κ x u w • v) := by
  have hg (a b : E) : beltramiMetric κ x a b =
      (beltramiDenominator κ x)⁻¹ * ⟪a,b⟫ -
        κ * (beltramiDenominator κ x)⁻¹ ^ 2 * ⟪x,a⟫ * ⟪x,b⟫ := by
    unfold beltramiMetric
    field_simp
  rw [hg,hg]
  simp only [beltramiCurvature,beltramiChristoffelVariation,beltramiChristoffel,
    inner_smul_right,inner_add_right,
    div_eq_mul_inv,inv_pow]
  rw [real_inner_comm u v]
  module

end OAI.Geometry.Nikodym
