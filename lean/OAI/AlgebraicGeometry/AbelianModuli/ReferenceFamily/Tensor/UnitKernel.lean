import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Unit Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.UnitKernel

noncomputable section

/-! A unit basis of the kernel after scalar extension gives injectivity
and exactness of the original tensor unit map, in the coordinates used
by the local contraction criterion. -/

universe u
open scoped TensorProduct

variable {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (d : M →ₗ[R] N) (u : R →ₗ[R] M) (hd : d.comp u = 0)

def tensorUnitCycle : (d.baseChange A).ker :=
  ⟨(1 : A) ⊗ₜ[R] u 1, by
    change (1 : A) ⊗ₜ[R] d (u 1) = 0
    rw [show d (u 1) = 0 from LinearMap.congr_fun hd 1, TensorProduct.tmul_zero]⟩

def tensorUnitKernelMap : A →ₗ[A] (d.baseChange A).ker :=
  LinearMap.toSpanSingleton A _ (tensorUnitCycle (A := A) d u hd)

theorem tensorUnitKernelMap_val (a : A) :
    (tensorUnitKernelMap d u hd a).val = a ⊗ₜ[R] u 1 := by
  change a • ((1 : A) ⊗ₜ[R] u 1) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem tensorUnitKernelMap_factor (a : A) :
    (tensorUnitKernelMap d u hd a).val = u.lTensor A ((TensorProduct.AlgebraTensorModule.rid R A A).symm a) := by
  rw [tensorUnitKernelMap_val, TensorProduct.AlgebraTensorModule.rid_symm_apply,
    LinearMap.lTensor_tmul]

theorem tensorUnitKernelMap_bijective_injective
    (h : Function.Bijective (tensorUnitKernelMap (A := A) d u hd)) :
    Function.Injective (u.lTensor A) := by
  let e := TensorProduct.AlgebraTensorModule.rid R A A
  intro x y hxy
  apply e.injective
  apply h.injective
  apply Subtype.ext
  rw [tensorUnitKernelMap_factor d u hd, tensorUnitKernelMap_factor d u hd,
    e.symm_apply_apply, e.symm_apply_apply]
  exact hxy

theorem tensorUnitKernelMap_bijective_exact
    (h : Function.Bijective (tensorUnitKernelMap (A := A) d u hd)) :
    (d.lTensor A).ker = (u.lTensor A).range := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := h.surjective (⟨x, hx⟩ : (d.baseChange A).ker)
    refine ⟨(TensorProduct.AlgebraTensorModule.rid R A A).symm a, ?_⟩
    exact (tensorUnitKernelMap_factor d u hd a).symm.trans (congrArg Subtype.val ha)
  · rintro ⟨y, rfl⟩
    have hzero := congrArg (fun f : R →ₗ[R] N => f.lTensor A) hd
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_zero] at hzero
    exact LinearMap.congr_fun hzero y

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.UnitKernel
