import OAI.Analysis.PDE.Elliptic.ContactMeasure
import OAI.Analysis.PDE.Elliptic.Determinant
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open Set InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The derivative of the gradient is the Riesz representative of the
genuine second Fréchet derivative. -/
theorem inner_fderiv_gradient {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    inner ℝ (fderiv ℝ (gradient f) x v) w = fderiv ℝ (fderiv ℝ f) x v w := by
  have hf₂ := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hd : fderiv ℝ (gradient f) x =
      (toDual ℝ E).symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) x) := by
    exact ((toDual ℝ E).symm.hasFDerivAt.comp x (hf₂ x).hasFDerivAt).fderiv
  rw [hd]
  change ((toDual ℝ E) ((toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) x v))) w = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem fderiv_gradient_isSymmetric {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    (fderiv ℝ (gradient f) x).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (fderiv ℝ (gradient f) x v) w = inner ℝ v (fderiv ℝ (gradient f) x w)
  rw [real_inner_comm (fderiv ℝ (gradient f) x w) v,
    inner_fderiv_gradient hf, inner_fderiv_gradient hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq v w

/-- Hessian positivity at a contact point, in the operator form needed by
the determinant estimate. -/
theorem fderiv_gradient_isPositive_of_contact {K : Set E} {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) {x : E} (hx : x ∈ lowerContactSet K f) :
    (fderiv ℝ (gradient f) x).toLinearMap.IsPositive := by
  refine ⟨fderiv_gradient_isSymmetric hf x, ?_⟩
  intro v
  change 0 ≤ inner ℝ (fderiv ℝ (gradient f) x v) v
  rw [inner_fderiv_gradient hf]
  exact hessian_nonneg_of_mem_lowerContactSet hf hx v

theorem trace_fderiv_gradient {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    LinearMap.trace ℝ E (fderiv ℝ (gradient f) x).toLinearMap = Laplacian.laplacian f x := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]
  change inner ℝ (fderiv ℝ (gradient f) x (b i)) (b i) = _
  rw [inner_fderiv_gradient hf]
  simp [iteratedFDeriv_two_apply]

/-- The actual Hessian Jacobian on the contact set is controlled by the
positive Laplacian to the ambient dimension. -/
theorem abs_det_fderiv_gradient_le_laplacian_pow {K : Set E} {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) {x : E} (hx : x ∈ lowerContactSet K f) :
    |(fderiv ℝ (gradient f) x).det| ≤ Laplacian.laplacian f x ^ Module.finrank ℝ E := by
  have h := abs_det_le_trace_pow_operator _ (fderiv_gradient_isPositive_of_contact hf hx)
  rwa [trace_fderiv_gradient hf] at h

end OAI.Analysis.PDE.Elliptic
