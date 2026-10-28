import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.BilinearMap

/-! # Contraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Contraction.CM.Construction

noncomputable section

/-!
The linear-algebra calculation used in CMReduction's composition step. The pairing
is an actual bilinear form, and the contraction is built from tensor-product
associators and evaluation. This module makes no cycle-algebraicity assumption.
-/

open scoped TensorProduct

variable {K U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Contract the two middle slots with the specified bilinear pairing. -/
def middleContraction (Q : V →ₗ[K] V →ₗ[K] K) :
    (U ⊗[K] V) ⊗[K] (V ⊗[K] W) →ₗ[K] U ⊗[K] W :=
  (TensorProduct.map (LinearMap.id : U →ₗ[K] U)
      (TensorProduct.lid K W).toLinearMap).comp
    ((TensorProduct.map (LinearMap.id : U →ₗ[K] U)
        (TensorProduct.map (TensorProduct.lift Q) (LinearMap.id : W →ₗ[K] W))).comp
      ((TensorProduct.map (LinearMap.id : U →ₗ[K] U)
          (TensorProduct.assoc K V V W).symm.toLinearMap).comp
        (TensorProduct.assoc K U V (V ⊗[K] W)).toLinearMap))

/-- The contraction multiplies the endpoint tensor by the middle pairing. -/
theorem middleContraction_tmul (Q : V →ₗ[K] V →ₗ[K] K)
    (u : U) (v v' : V) (w : W) :
    middleContraction Q ((u ⊗ₜ[K] v) ⊗ₜ[K] (v' ⊗ₜ[K] w)) =
      Q v v' • (u ⊗ₜ[K] w) := by
  simp [middleContraction, TensorProduct.tmul_smul]

/-- A nonzero middle pairing lets one recover the endpoint from its
contracted multiple in any linear subspace, including a cycle-class image. -/
theorem endpoint_mem_of_contraction_mem (Q : V →ₗ[K] V →ₗ[K] K)
    (S : Submodule K (U ⊗[K] W))
    (u : U) (v v' : V) (w : W)
    (hQ : Q v v' ≠ 0)
    (h : middleContraction Q ((u ⊗ₜ[K] v) ⊗ₜ[K] (v' ⊗ₜ[K] w)) ∈ S) :
    u ⊗ₜ[K] w ∈ S := by
  rw [middleContraction_tmul] at h
  have hscaled := S.smul_mem (Q v v')⁻¹ h
  simpa only [smul_smul, inv_mul_cancel₀ hQ, one_smul] using hscaled

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Contraction.CM.Construction
