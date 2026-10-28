import OAI.Analysis.PDE.Elliptic.TraceCoercivity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def radialGaussian (a : ℝ) (x : E) : ℝ := Real.exp (-a * ‖x‖ ^ 2)

omit [FiniteDimensional ℝ E] in
theorem radialGaussian_contDiff (a : ℝ) : ContDiff ℝ ⊤ (radialGaussian (E := E) a) := by
  exact Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem radialGaussian_pos (a : ℝ) (x : E) : 0 < radialGaussian a x := Real.exp_pos _

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_radialGaussian (a : ℝ) (x : E) :
    HasFDerivAt (radialGaussian a) ((-2 * a * radialGaussian a x) • innerSL ℝ x) x := by
  have h : HasFDerivAt (radialGaussian a)
      (radialGaussian a x • (-a • ((2 : ℕ) • innerSL ℝ x))) x :=
    (Real.hasDerivAt_exp (-a * ‖x‖ ^ 2)).comp_hasFDerivAt x
      (((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (-a))
  have heq : radialGaussian a x • (-a • ((2 : ℕ) • innerSL ℝ x)) =
      (-2 * a * radialGaussian a x) • innerSL ℝ x := by
    ext v
    simp only [smul_apply, smul_eq_mul, two_smul, add_apply]
    ring
  rwa [heq] at h

theorem gradient_radialGaussian (a : ℝ) (x : E) :
    gradient (radialGaussian a) x = (-2 * a * radialGaussian a x) • x := by
  rw [gradient, (hasFDerivAt_radialGaussian a x).fderiv]
  change (toDual ℝ E).symm ((-2 * a * radialGaussian a x) • (toDual ℝ E) x) = _
  rw [map_smul, LinearIsometryEquiv.symm_apply_apply]

/-- The complete Gaussian Hessian as an actual continuous linear operator. -/
theorem fderiv_gradient_radialGaussian (a : ℝ) (x : E) :
    fderiv ℝ (gradient (radialGaussian a)) x =
      (-2 * a * radialGaussian a x) • ContinuousLinearMap.id ℝ E +
        (4 * a ^ 2 * radialGaussian a x) • rankOne ℝ x x := by
  have hgrad : gradient (radialGaussian (E := E) a) =
      fun y ↦ (-2 * a * radialGaussian a y) • y := funext (gradient_radialGaussian a)
  rw [hgrad]
  have h : HasFDerivAt (fun y : E ↦ (-2 * a * radialGaussian a y) • y)
      ((-2 * a * radialGaussian a x) • ContinuousLinearMap.id ℝ E +
        ((-2 * a) • ((-2 * a * radialGaussian a x) • innerSL ℝ x)).smulRight x) x :=
    ((hasFDerivAt_radialGaussian a x).const_mul (-2 * a)).smul (hasFDerivAt_id x)
  rw [h.fderiv]
  ext v
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, rankOne_apply, smul_smul, smul_eq_mul]
  module

theorem trace_comp_scalar_id_rankOne (A : E →L[ℝ] E) (x : E) (c d : ℝ) :
    LinearMap.trace ℝ E (A.comp
      (c • ContinuousLinearMap.id ℝ E + d • rankOne ℝ x x)).toLinearMap =
      c * LinearMap.trace ℝ E A.toLinearMap + d * inner ℝ x (A x) := by
  have hop : A.comp (c • ContinuousLinearMap.id ℝ E + d • rankOne ℝ x x) =
      c • A + d • rankOne ℝ (A x) x := by
    ext v
    simp [ContinuousLinearMap.comp_apply, rankOne_apply]
  rw [hop]
  change LinearMap.trace ℝ E
    (c • A.toLinearMap + d • (rankOne ℝ (A x) x).toLinearMap) = _
  rw [map_add, map_smul, map_smul, trace_rankOne]
  rfl

theorem ellipticTrace_radialGaussian (A : E → E →L[ℝ] E) (a : ℝ) (x : E) :
    ellipticTrace A (radialGaussian a) x =
      2 * a * radialGaussian a x *
        (2 * a * inner ℝ x (A x x) - LinearMap.trace ℝ E (A x).toLinearMap) := by
  rw [ellipticTrace, fderiv_gradient_radialGaussian, trace_comp_scalar_id_rankOne]
  ring

end OAI.Analysis.PDE.Elliptic
