import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Split Tensor Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitTensorInjection

noncomputable section

/-! A split linear inclusion stays injective after any scalar extension. -/
open scoped TensorProduct
universe u

theorem baseChange_injective_of_linear_retraction
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (i : M →ₗ[R] N) (r : N →ₗ[R] M) (hr : r.comp i = LinearMap.id) :
    Function.Injective (i.baseChange A) := by
  have h : (r.baseChange A).comp (i.baseChange A) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
  have hi : Function.LeftInverse (r.baseChange A) (i.baseChange A) :=
    fun x => congrArg (fun k => k x) h
  exact hi.injective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitTensorInjection
