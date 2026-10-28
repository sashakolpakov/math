import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-! # Coefficients -/

namespace OAI.Analysis.DifferentialForms.Manifold.Coefficients.Comparison

noncomputable section

/-!
# Real and imaginary components of actual complex differential forms

Postcomposition by a continuous real-linear map preserves smoothness and
commutes with exterior differentiation. The latter statement requires actual
differentiability, because the totalized derivative of a nondifferentiable map
need not commute with a noninjective projection.
-/

open scoped ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n : ℕ}

/-- Change the values of a real differential form by a continuous linear map. -/
def postcomposeForm (T : F →L[ℝ] G) (form : E → E [⋀^Fin n]→L[ℝ] F) :
    E → E [⋀^Fin n]→L[ℝ] G :=
  fun x => T.compContinuousAlternatingMap (form x)

@[simp]
theorem postcomposeForm_apply (T : F →L[ℝ] G)
    (form : E → E [⋀^Fin n]→L[ℝ] F) (x : E) (v : Fin n → E) :
    postcomposeForm T form x v = T (form x v) := rfl

/-- Smoothness of the original form implies smoothness of its components. -/
theorem contDiff_postcomposeForm (T : F →L[ℝ] G)
    (form : E → E [⋀^Fin n]→L[ℝ] F) {r : WithTop ℕ∞}
    (hform : ContDiff ℝ r form) : ContDiff ℝ r (postcomposeForm T form) :=
  (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E F G (Fin n) T).contDiff.comp hform

/-- Exterior differentiation commutes with a fixed map on the coefficients. -/
theorem extDeriv_postcomposeForm (T : F →L[ℝ] G)
    (form : E → E [⋀^Fin n]→L[ℝ] F) {x : E}
    (hform : DifferentiableAt ℝ form x) :
    extDeriv (postcomposeForm T form) x = T.compContinuousAlternatingMap (extDeriv form x) := by
  let L := ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E F G (Fin n) T
  have hd : fderiv ℝ (postcomposeForm T form) x = L.comp (fderiv ℝ form x) :=
    (L.hasFDerivAt.comp x hform.hasFDerivAt).fderiv
  ext v
  simp [extDeriv, hd, ContinuousAlternatingMap.alternatizeUncurryFin_apply, L]

/-- The real component of a complex-valued real differential form. -/
def realForm (form : E → E [⋀^Fin n]→L[ℝ] ℂ) : E → E [⋀^Fin n]→L[ℝ] ℝ :=
  postcomposeForm Complex.reCLM form

/-- The imaginary component of a complex-valued real differential form. -/
def imagForm (form : E → E [⋀^Fin n]→L[ℝ] ℂ) : E → E [⋀^Fin n]→L[ℝ] ℝ :=
  postcomposeForm Complex.imCLM form

@[simp]
theorem realForm_apply (form : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) (v : Fin n → E) :
    realForm form x v = (form x v).re := rfl

@[simp]
theorem imagForm_apply (form : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) (v : Fin n → E) :
    imagForm form x v = (form x v).im := rfl

theorem contDiff_realForm (form : E → E [⋀^Fin n]→L[ℝ] ℂ) {r : WithTop ℕ∞}
    (hform : ContDiff ℝ r form) : ContDiff ℝ r (realForm form) :=
  contDiff_postcomposeForm Complex.reCLM form hform

theorem contDiff_imagForm (form : E → E [⋀^Fin n]→L[ℝ] ℂ) {r : WithTop ℕ∞}
    (hform : ContDiff ℝ r form) : ContDiff ℝ r (imagForm form) :=
  contDiff_postcomposeForm Complex.imCLM form hform

theorem extDeriv_realForm (form : E → E [⋀^Fin n]→L[ℝ] ℂ) {x : E}
    (hform : DifferentiableAt ℝ form x) :
    extDeriv (realForm form) x = realForm (extDeriv form) x :=
  extDeriv_postcomposeForm Complex.reCLM form hform

theorem extDeriv_imagForm (form : E → E [⋀^Fin n]→L[ℝ] ℂ) {x : E}
    (hform : DifferentiableAt ℝ form x) :
    extDeriv (imagForm form) x = imagForm (extDeriv form) x :=
  extDeriv_postcomposeForm Complex.imCLM form hform

/-- Both real component equations are necessary and sufficient for equality. -/
theorem complexForm_ext {form other : E → E [⋀^Fin n]→L[ℝ] ℂ}
    (hre : realForm form = realForm other) (him : imagForm form = imagForm other) : form = other := by
  funext x
  ext v
  apply Complex.ext
  · exact congrFun (congrFun (congrArg (fun f => fun y w => f y w) hre) x) v
  · exact congrFun (congrFun (congrArg (fun f => fun y w => f y w) him) x) v

end

end OAI.Analysis.DifferentialForms.Manifold.Coefficients.Comparison
