import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Finite Tensor Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FiniteTensorCoordinates.LargeFiniteTensorCoordinates

noncomputable section

/-! # Finite coefficient bases on the original large cohomology modules -/

open scoped TensorProduct

universe u

variable (R ξ V : Type u) [CommRing R] [Fintype ξ] [AddCommGroup V] [Module R V]
  (b : Module.Basis ξ R V)
  (M N : Type (u + 2)) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

def equiv : M ⊗[R] V ≃ₗ[R] (ξ → M) := by
  classical
  exact (TensorProduct.congr (LinearEquiv.refl R M) b.equivFun).trans
    (TensorProduct.piScalarRight R R M ξ)

theorem tmul (m : M) (v : V) (i : ξ) : equiv R ξ V b M (m ⊗ₜ[R] v) i = b.equivFun v i • m := rfl

theorem naturality (f : M →ₗ[R] N) :
    (equiv R ξ V b N).toLinearMap.comp (TensorProduct.map f LinearMap.id) =
      (LinearMap.pi (fun i => f.comp (LinearMap.proj i))).comp (equiv R ξ V b M).toLinearMap := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro v
  funext i
  change b.equivFun v i • f m = f (b.equivFun v i • m)
  exact (f.map_smul _ _).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FiniteTensorCoordinates.LargeFiniteTensorCoordinates
