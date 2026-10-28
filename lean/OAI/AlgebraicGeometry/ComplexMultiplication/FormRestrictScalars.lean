import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-! # Form Restrict Scalars -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.FormRestrictScalars

noncomputable section

/-! # Exterior differentiation and restriction from complex to real scalars

The actual exterior derivatives use the same alternating-sum normalization.
For a complex-differentiable covector field, its real exterior derivative is
the scalar restriction of its complex exterior derivative.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {p : ℕ} {x : E}

/-- Scalar restriction retains the complete exterior derivative, without a factor. -/
theorem extDeriv_restrictScalars
    (ω : E → E [⋀^Fin p]→L[ℂ] ℂ) (h : DifferentiableAt ℂ ω x) :
    extDeriv (fun y => (ω y).restrictScalars ℝ) x =
      (extDeriv ω x).restrictScalars ℝ := by
  let R : (E [⋀^Fin p]→L[ℂ] ℂ) →L[ℝ] (E [⋀^Fin p]→L[ℝ] ℂ) :=
    (ContinuousAlternatingMap.restrictScalarsLI ℝ).toContinuousLinearMap
  have hr : DifferentiableAt ℝ (fun y => (ω y).restrictScalars ℝ) x :=
    R.differentiableAt.comp x (h.restrictScalars ℝ)
  apply ContinuousAlternatingMap.ext
  intro v
  change extDeriv (fun y => (ω y).restrictScalars ℝ) x v = extDeriv ω x v
  rw [extDeriv_apply hr, extDeriv_apply h]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := h.continuousAlternatingMap_apply_const (i.removeNth v)
  exact congrArg (fun g => g (v i)) (hi.fderiv_restrictScalars ℝ)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.FormRestrictScalars
