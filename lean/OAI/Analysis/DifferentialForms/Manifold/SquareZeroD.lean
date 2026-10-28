import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivative
import OAI.Analysis.DifferentialForms.Manifold.SquareZero

/-! # Square Zero D -/

namespace OAI.Analysis.DifferentialForms.Manifold

/-! The actual exterior derivative squares to zero on bundled smooth forms.

The derivative is the complex-linear map constructed from real differentiation.
No regularity hypotheses remain: the required smoothness is the defining
property of each `SmoothForm`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

@[simp]
theorem Basic.SmoothForm.d_d (form : Basic.SmoothForm E n) : Basic.SmoothForm.d (Basic.SmoothForm.d form) = 0 := by
  apply Subtype.ext
  change extDeriv (extDeriv (form : Basic.RawForm E n)) = 0
  exact SquareZero.extDeriv_extDeriv_of_contDiff form.smooth

theorem Basic.SmoothForm.d_comp_d (n : ℕ) :
    (Basic.SmoothForm.d : Basic.SmoothForm E (n + 1) →ₗ[ℂ] Basic.SmoothForm E (n + 2)).comp
      (Basic.SmoothForm.d : Basic.SmoothForm E n →ₗ[ℂ] Basic.SmoothForm E (n + 1)) = 0 := by
  apply LinearMap.ext
  intro form
  exact Basic.SmoothForm.d_d form

theorem Basic.SmoothForm.range_d_le_ker_d (n : ℕ) :
    LinearMap.range (Basic.SmoothForm.d : Basic.SmoothForm E n →ₗ[ℂ] Basic.SmoothForm E (n + 1)) ≤
      LinearMap.ker (Basic.SmoothForm.d : Basic.SmoothForm E (n + 1) →ₗ[ℂ] Basic.SmoothForm E (n + 2)) := by
  rintro form ⟨previousForm, rfl⟩
  exact Basic.SmoothForm.d_d previousForm

end OAI.Analysis.DifferentialForms.Manifold
