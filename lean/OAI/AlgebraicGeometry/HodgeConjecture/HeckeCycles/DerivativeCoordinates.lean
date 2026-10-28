import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Projection

/-! # Derivative Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DerivativeCoordinates.CM

noncomputable section

/-! Coordinates of the actual continuous theta derivative under a
linear change of its variable. These turn PoissonAutomorphy's covector formula into
the vector formula used in the source's prescribed period graph. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Projection.CM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem apply_eq_sum (f : (ι → ℂ) →L[ℂ] ℂ) (x : ι → ℂ) :
    f x = ∑ i, x i * Theta.Projection.CM.coefficients f i := by
  have h := LinearMap.congr_fun
    ((LinearEquiv.piRing ℂ ℂ ι ℂ).symm_apply_apply f.toLinearMap) x
  simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply,
    smul_eq_mul, Theta.Projection.CM.coefficients_apply, ContinuousLinearMap.coe_coe] using h.symm

theorem coefficients_comp_matrix (f : (ι → ℂ) →L[ℂ] ℂ) (M : Matrix ι ι ℂ) :
    Theta.Projection.CM.coefficients (f.comp (Theta.Projection.CM.matrixOperator M)) = M.transpose.mulVec (Theta.Projection.CM.coefficients f) := by
  funext i
  rw [Theta.Projection.CM.coefficients_apply, ContinuousLinearMap.comp_apply, apply_eq_sum]
  change (∑ j, M.mulVec (Pi.single i 1) j * Theta.Projection.CM.coefficients f j) = _
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem coefficients_of_covariance
    (f h : (ι → ℂ) →L[ℂ] ℂ) (M : Matrix ι ι ℂ) (c : ℂ)
    (hM : IsUnit M.det)
    (he : f.comp (Theta.Projection.CM.matrixOperator M⁻¹.transpose) = c • h) :
    Theta.Projection.CM.coefficients f = c • M.mulVec (Theta.Projection.CM.coefficients h) := by
  have hc := congrArg Theta.Projection.CM.coefficients he
  rw [coefficients_comp_matrix, Matrix.transpose_transpose, map_smul] at hc
  have hm := congrArg M.mulVec hc
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec,
    Matrix.mulVec_smul] at hm
  exact hm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DerivativeCoordinates.CM
