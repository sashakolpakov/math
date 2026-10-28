import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Dolbeault Function Kernel -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultFunctionKernel

noncomputable section

/-! The actual antiholomorphic derivative vanishes exactly for a complex differentiable function. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E F : Type*)
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def complexLinearDerivativePart (D : E →L[ℝ] F) : E →L[ℂ] F where
  toFun := OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E F D
  map_add' x y := map_add _ x y
  map_smul' c x := OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply_smul E F D c x
  cont := (OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E F D).continuous

theorem complexAntilinearPart_restrictScalars (D : E →L[ℂ] F) :
    OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E F (D.restrictScalars ℝ) = 0 := by
  ext x
  change (1 / 2 : ℂ) • (D x + Complex.I • D (Complex.I • x)) = 0
  rw [map_smul, smul_smul, Complex.I_mul_I, neg_one_smul, add_neg_cancel, smul_zero]

theorem complexAntilinearPart_eq_zero_iff (D : E →L[ℝ] F) :
    OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E F D = 0 ↔ ∃ L : E →L[ℂ] F, L.restrictScalars ℝ = D := by
  constructor
  · intro h
    refine ⟨complexLinearDerivativePart E F D, ?_⟩
    have he := OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexDerivativeParts_add E F D
    rw [h, add_zero] at he
    exact he
  · rintro ⟨L, rfl⟩
    exact complexAntilinearPart_restrictScalars E F L

variable {E F} {f : E → F} {x : E}

theorem differentiableAt_complex_iff_antilinear_zero (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℂ f x ↔ OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E F (fderiv ℝ f x) = 0 := by
  rw [differentiableAt_iff_restrictScalars ℝ hf, complexAntilinearPart_eq_zero_iff]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultFunctionKernel
