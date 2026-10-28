import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Flat Joint Injection -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatJointInjection.Construction

noncomputable section

/-! Flat scalar extension preserves joint injectivity of two linear maps. -/

open TensorProduct

universe u v w w₁ w₂

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  [Module.Flat R S]
  {M : Type w} [AddCommGroup M] [Module R M]
  {N : Type w₁} [AddCommGroup N] [Module R N]
  {P : Type w₂} [AddCommGroup P] [Module R P]

/-- Tensoring a joint injection by a flat algebra gives the joint injection of the
two actual scalar-extended maps. -/
theorem baseChange_prod_injective (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (h : Function.Injective (f.prod g)) :
    Function.Injective ((f.baseChange S).prod (g.baseChange S)) := by
  have hj : Function.Injective ((f.prod g).baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap (f.prod g) h
  have he : (f.baseChange S).prod (g.baseChange S) =
      (prodRight R S S N P).toLinearMap.comp ((f.prod g).baseChange S) := by
    ext s <;> rfl
  rw [he]
  exact (prodRight R S S N P).injective.comp hj

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatJointInjection.Construction
