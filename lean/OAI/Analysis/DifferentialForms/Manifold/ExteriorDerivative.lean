import OAI.Analysis.DifferentialForms.Manifold.Basic
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth
import OAI.Analysis.DifferentialForms.Manifold.ComplexLinearity

/-! # Exterior Derivative -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Exterior derivative of bundled smooth complex-valued real forms

The differential is mathlib's actual exterior derivative on a real normed
space. Smoothness and complex linearity are proved before bundling it as a
linear map. This local normed-space construction does not supply a global
de Rham comparison theorem or a formalization of the Hodge conjecture.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- Exterior differentiation, bundled as a complex-linear map between the
actual spaces of smooth complex-valued forms. -/
def Basic.SmoothForm.d : Basic.SmoothForm E n →ₗ[ℂ] Basic.SmoothForm E (n + 1) where
  toFun ω := ⟨extDeriv (ω : Basic.RawForm E n), ExteriorDerivativeSmooth.contDiff_extDeriv_infty ω.smooth⟩
  map_add' ω η := by
    apply Subtype.ext
    funext x
    exact extDeriv_add
      ((ω.smooth.differentiable (by simp)).differentiableAt)
      ((η.smooth.differentiable (by simp)).differentiableAt)
  map_smul' c ω := by
    apply Subtype.ext
    funext x
    exact ComplexLinearity.extDeriv_complex_smul c (ω : Basic.RawForm E n) x

/-- The bundled differential has exactly the underlying exterior derivative. -/
@[simp]
theorem Basic.SmoothForm.coe_d (ω : Basic.SmoothForm E n) :
    ((Basic.SmoothForm.d ω : Basic.SmoothForm E (n + 1)) : Basic.RawForm E (n + 1)) =
      extDeriv (ω : Basic.RawForm E n) := rfl

/-- Pointwise reduction of the bundled differential. -/
@[simp]
theorem Basic.SmoothForm.d_apply (ω : Basic.SmoothForm E n) (x : E) :
    Basic.SmoothForm.d ω x = extDeriv (ω : Basic.RawForm E n) x := rfl

/-- The standard alternating sum formula for the exterior derivative; this
fixes the normalization of the bundled differential explicitly. -/
theorem Basic.SmoothForm.d_apply_vectors (ω : Basic.SmoothForm E n) (x : E) (v : Fin (n + 1) → E) :
    Basic.SmoothForm.d ω x v = ∑ i, (-1 : ℤ) ^ i.val •
      fderiv ℝ (fun y => ω y (i.removeNth v)) x (v i) := by
  exact extDeriv_apply ((ω.smooth.differentiable (by simp)).differentiableAt) v

end

end OAI.Analysis.DifferentialForms.Manifold
