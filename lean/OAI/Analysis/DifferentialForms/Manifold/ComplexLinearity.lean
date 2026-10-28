import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Complex Linearity -/

namespace OAI.Analysis.DifferentialForms.Manifold.ComplexLinearity

/-!
# Complex scalar compatibility of real exterior differentiation

The tangent variables are real and the values are complex. Consequently the
scalar rule needed by the complex de Rham complex is more general than the
same-field `extDeriv_smul` rule.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- Real exterior differentiation commutes with multiplication by a constant
complex number. The standard zero convention for derivatives makes a separate
differentiability hypothesis unnecessary. -/
theorem extDeriv_complex_smul (c : ℂ)
    (ω : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) :
    extDeriv (c • ω) x = c • extDeriv ω x := by
  unfold extDeriv
  rw [fderiv_const_smul_field (𝕜 := ℝ) (f := ω) c]
  exact ContinuousAlternatingMap.alternatizeUncurryFin_smul c _

/-- Function-valued version of complex scalar compatibility. -/
theorem extDeriv_complex_smul_eq (c : ℂ)
    (ω : E → E [⋀^Fin n]→L[ℝ] ℂ) :
    extDeriv (c • ω) = c • extDeriv ω := by
  funext x
  exact extDeriv_complex_smul c ω x

/-- Complex scalar compatibility in a set with unique real derivatives. -/
theorem extDerivWithin_complex_smul (c : ℂ)
    (ω : E → E [⋀^Fin n]→L[ℝ] ℂ) {s : Set E} {x : E}
    (hs : UniqueDiffWithinAt ℝ s x) :
    extDerivWithin (c • ω) s x = c • extDerivWithin ω s x := by
  unfold extDerivWithin
  rw [fderivWithin_const_smul_field (𝕜 := ℝ) (f := ω) c hs]
  exact ContinuousAlternatingMap.alternatizeUncurryFin_smul c _

end OAI.Analysis.DifferentialForms.Manifold.ComplexLinearity
