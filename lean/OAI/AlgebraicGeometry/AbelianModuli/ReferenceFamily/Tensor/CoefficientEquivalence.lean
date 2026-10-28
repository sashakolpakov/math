import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Exact.Basic

/-! # Coefficient Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.CoefficientEquivalence

noncomputable section

/-! Equivalent coefficient modules preserve injectivity and the
degree-zero exactness conditions under tensor product. -/

open scoped TensorProduct

universe u
variable {R A B U M N : Type u} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup U] [Module R U] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem tensorCoefficientEquiv_natural (e : A ≃ₗ[R] B) (d : M →ₗ[R] N) :
    (d.lTensor B).comp (e.rTensor M).toLinearMap =
      (e.rTensor N).toLinearMap.comp (d.lTensor A) := by
  change (d.lTensor B).comp (e.toLinearMap.rTensor M) =
    (e.toLinearMap.rTensor N).comp (d.lTensor A)
  rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

theorem tensorCoefficientEquiv_injective (e : A ≃ₗ[R] B) (u : U →ₗ[R] M)
    (hu : Function.Injective (u.lTensor A)) : Function.Injective (u.lTensor B) := by
  intro x y hxy
  apply (e.symm.rTensor U).injective
  apply hu
  have hx := LinearMap.congr_fun (tensorCoefficientEquiv_natural e.symm u) x
  have hy := LinearMap.congr_fun (tensorCoefficientEquiv_natural e.symm u) y
  exact hx.trans ((congrArg (e.symm.rTensor M) hxy).trans hy.symm)

theorem tensorCoefficientEquiv_exact (e : A ≃ₗ[R] B) (u : U →ₗ[R] M) (d : M →ₗ[R] N)
    (h : (d.lTensor A).ker = (u.lTensor A).range) :
    (d.lTensor B).ker = (u.lTensor B).range := by
  have hex : Function.Exact (u.lTensor A) (d.lTensor A) := LinearMap.exact_iff.mpr h
  have h' := (LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    (u.lTensor A) (d.lTensor A) (u.lTensor B) (d.lTensor B)
    (e.rTensor U).toLinearMap (e.rTensor M).toLinearMap (e.rTensor N).toLinearMap
    (tensorCoefficientEquiv_natural e u) (tensorCoefficientEquiv_natural e d)
    (e.rTensor U).surjective (e.rTensor M).bijective (e.rTensor N).injective).mp hex
  exact LinearMap.exact_iff.mp h'

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.CoefficientEquivalence
