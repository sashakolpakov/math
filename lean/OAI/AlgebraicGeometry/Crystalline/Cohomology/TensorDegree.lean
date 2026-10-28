import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Tensor Degree -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorDegree.TensorDegreeZero

noncomputable section

/-! # The degree-zero tensor term and its coefficient module -/

open scoped TensorProduct

universe u

variable (R σ M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

def equiv : Koszul.Tensor.KoszulTensor.Term R σ M 0 ≃ₗ[R] M :=
  (TensorProduct.congr (LinearEquiv.refl R M) (exteriorPower.zeroEquiv R (σ →₀ R))).trans
    (TensorProduct.rid R M)

theorem equiv_tmul (m : M) (ω : ⋀[R]^0 (σ →₀ R)) :
    equiv R σ M (m ⊗ₜ[R] ω) = exteriorPower.zeroEquiv R (σ →₀ R) ω • m := rfl

theorem equiv_symm (m : M) :
    (equiv R σ M).symm m = m ⊗ₜ[R] (exteriorPower.zeroEquiv R (σ →₀ R)).symm 1 := by
  apply (equiv R σ M).injective
  rw [LinearEquiv.apply_symm_apply, equiv_tmul, LinearEquiv.apply_symm_apply, one_smul]

theorem conjugate (f : Module.End R M) :
    ((equiv R σ M).symm.toLinearMap.comp f).comp (equiv R σ M).toLinearMap =
      TensorProduct.map f LinearMap.id := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro ω
  change (equiv R σ M).symm (f (equiv R σ M (m ⊗ₜ[R] ω))) = f m ⊗ₜ[R] ω
  apply (equiv R σ M).injective
  rw [LinearEquiv.apply_symm_apply, equiv_tmul, equiv_tmul, map_smul]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorDegree.TensorDegreeZero
