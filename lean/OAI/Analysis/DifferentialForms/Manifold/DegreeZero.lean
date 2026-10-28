import OAI.Analysis.DifferentialForms.Manifold.Functions
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivative

/-! # Degree Zero -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Degree-zero forms are smooth functions

This identifies actual smooth complex-valued functions on a real normed space
with its smooth zero-forms. Under this identification the exterior derivative
is exactly the Fréchet derivative, viewed as a one-form.
-/

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section

/-- Regard a smooth function as a smooth zero-form. -/
def Functions.SmoothFunction.toZeroForm (f : Functions.SmoothFunction E) : Basic.SmoothForm E 0 :=
  ⟨fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f x), by
    change ContDiff ℝ ∞
      ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)) ∘ (f : E → ℂ))
    exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.comp
      f.smooth⟩

@[simp]
theorem Functions.SmoothFunction.toZeroForm_apply (f : Functions.SmoothFunction E) (x : E) (v : Fin 0 → E) :
    f.toZeroForm x v = f x := rfl

end

section

/-- Evaluate the unique empty tuple of tangent vectors in a zero-form. -/
def Basic.SmoothForm.toSmoothFunction (form : Basic.SmoothForm E 0) : Functions.SmoothFunction E :=
  ⟨fun x => form x 0, by
    change ContDiff ℝ ∞
      ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).symm ∘ (form : Basic.RawForm E 0))
    exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).symm.contDiff.comp
      form.smooth⟩

@[simp]
theorem Basic.SmoothForm.toSmoothFunction_apply (form : Basic.SmoothForm E 0) (x : E) :
    form.toSmoothFunction x = form x 0 := rfl

end

/-- Smooth zero-forms and smooth functions are canonically complex-linearly equivalent. -/
def DegreeZero.smoothFunctionZeroFormEquiv : Functions.SmoothFunction E ≃ₗ[ℂ] Basic.SmoothForm E 0 where
  toFun := Functions.SmoothFunction.toZeroForm
  invFun := Basic.SmoothForm.toSmoothFunction
  left_inv f := by
    apply Functions.SmoothFunction.ext
    intro x
    rfl
  right_inv form := by
    apply Basic.SmoothForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    change form x 0 = form x v
    congr 1
    exact Subsingleton.elim _ _
  map_add' f g := by
    apply Basic.SmoothForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    rfl
  map_smul' c f := by
    apply Basic.SmoothForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    rfl

section

/-- Converting a function to a zero-form and evaluating the empty tuple recovers it. -/
@[simp]
theorem Functions.SmoothFunction.toSmoothFunction_toZeroForm (f : Functions.SmoothFunction E) :
    f.toZeroForm.toSmoothFunction = f :=
  DegreeZero.smoothFunctionZeroFormEquiv.left_inv f

/-- The derivative of a zero-form is the one-form determined by `fderiv`. -/
theorem Functions.SmoothFunction.d_toZeroForm (f : Functions.SmoothFunction E) (x : E) :
    Basic.SmoothForm.d f.toZeroForm x =
      ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)
        (fderiv ℝ (f : E → ℂ) x) :=
  extDeriv_constOfIsEmpty (f : E → ℂ) x

/-- Evaluate the exterior derivative of a smooth function on a tangent vector. -/
@[simp]
theorem Functions.SmoothFunction.d_toZeroForm_apply (f : Functions.SmoothFunction E) (x : E) (v : Fin 1 → E) :
    Basic.SmoothForm.d f.toZeroForm x v = fderiv ℝ (f : E → ℂ) x (v 0) := by
  rw [Functions.SmoothFunction.d_toZeroForm]
  rfl

end

/-- Evaluating a zero-form and reconstructing its empty alternating map recovers it. -/
@[simp]
theorem Basic.SmoothForm.toZeroForm_toSmoothFunction (form : Basic.SmoothForm E 0) :
    form.toSmoothFunction.toZeroForm = form :=
  DegreeZero.smoothFunctionZeroFormEquiv.right_inv form

end

end OAI.Analysis.DifferentialForms.Manifold
