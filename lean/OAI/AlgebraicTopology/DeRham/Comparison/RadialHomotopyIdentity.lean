import OAI.AlgebraicTopology.DeRham.Comparison.RadialCurryDerivative
import OAI.AlgebraicTopology.DeRham.Comparison.RadialExteriorIntegral
import OAI.AlgebraicTopology.DeRham.Comparison.RadialFlow

/-! # Radial Homotopy Identity -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RadialHomotopyIdentity

noncomputable section

/-!
# The radial homotopy identity in every positive degree

The proof uses differentiation of the actual parameter integral, the
alternating-map cancellation identity, and the fundamental theorem of calculus
for radial dilations.
-/

set_option backward.isDefEq.respectTransparency false

open _root_.MeasureTheory _root_.ContinuousAlternatingMap
open scoped Interval

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ}

local instance radialIdentityAltNormedGroup :
    NormedAddCommGroup (E [⋀^Fin n]→L[ℝ] F) := inferInstance
local instance radialIdentityAltNormedSpace :
    NormedSpace ℝ (E [⋀^Fin n]→L[ℝ] F) := inferInstance
local instance radialIdentityClmNormedGroup :
    NormedAddCommGroup (E →L[ℝ] (E [⋀^Fin n]→L[ℝ] F)) := inferInstance

/-- Pointwise cancellation of the two integrands in the homotopy formula. -/
theorem radialIntegrand_homotopy_identity
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} {x : E} (t : ℝ)
    (hform : DifferentiableAt ℝ form (t • x)) :
    extDeriv (fun y ↦ RadialOne.radialIntegrand form y t) x +
      RadialOne.radialIntegrand (extDeriv form) x t = RadialFlow.radialFlowDerivative form x t := by
  rw [extDeriv, RadialCurryDerivative.fderiv_radialIntegrand_aux t hform]
  exact RadialOne.weighted_alternatize_contractionDerivative_add
    (form (t • x)) (fderiv ℝ form (t • x)) x t

@[simp]
theorem radialHomotopy_zero (x : E) :
    RadialOne.radialHomotopy (0 : E → E [⋀^Fin (n + 1)]→L[ℝ] F) x = 0 := by
  simp [RadialOne.radialHomotopy, RadialOne.radialIntegrand]

variable [FiniteDimensional ℝ E] [CompleteSpace F]

/-- The genuine radial homotopy identity `dK + Kd = id` on every positive
degree, for continuously differentiable forms on a finite-dimensional real
normed space. -/
theorem radialHomotopy_identity
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : ContDiff ℝ 1 form) (x : E) :
    extDeriv (RadialOne.radialHomotopy form) x + RadialOne.radialHomotopy (extDeriv form) x = form x := by
  have hdform : Continuous (extDeriv form) :=
    (alternatizeUncurryFinCLM ℝ E F).continuous.comp
      (hform.continuous_fderiv (by norm_num))
  have hintDerivative := RadialExteriorIntegral.intervalIntegrable_fderiv_radialIntegrand hform x
  have hintExterior : IntervalIntegrable
      (fun t ↦ extDeriv (fun y ↦ RadialOne.radialIntegrand form y t) x) volume 0 1 := by
    exact ⟨(alternatizeUncurryFinCLM ℝ E F).integrable_comp hintDerivative.1,
      (alternatizeUncurryFinCLM ℝ E F).integrable_comp hintDerivative.2⟩
  rw [RadialExteriorIntegral.extDeriv_radialHomotopy_eq_integral hform x, RadialOne.radialHomotopy]
  rw [← intervalIntegral.integral_add hintExterior (RadialOne.intervalIntegrable_radialIntegrand hdform x)]
  calc
    _ = ∫ t in (0 : ℝ)..1, RadialFlow.radialFlowDerivative form x t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact radialIntegrand_homotopy_identity t (hform.differentiable (by norm_num) (t • x))
    _ = form x := RadialFlow.integral_radialFlowDerivative hform x

/-- The radial primitive has exterior derivative equal to any closed
positive-degree form. -/
theorem extDeriv_radialHomotopy_of_closed
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : ContDiff ℝ 1 form)
    (hclosed : extDeriv form = 0) :
    extDeriv (RadialOne.radialHomotopy form) = form := by
  funext x
  have h := radialHomotopy_identity hform x
  simpa only [hclosed, radialHomotopy_zero, add_zero] using h

end

end OAI.AlgebraicTopology.DeRham.Comparison.RadialHomotopyIdentity
