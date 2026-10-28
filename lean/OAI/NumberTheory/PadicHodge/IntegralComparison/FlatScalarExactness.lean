import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Flat Scalar Exactness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlatScalarExactness

noncomputable section

/-! Flat modules preserve the exact scalar-multiplication sequences of their coefficient ring. -/

universe u v

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M]
  (a b : R)

theorem exact (h : Function.Exact (DistribSMul.toLinearMap R R a) (DistribSMul.toLinearMap R R b)) :
    Function.Exact (DistribSMul.toLinearMap R M a) (DistribSMul.toLinearMap R M b) := by
  have ht := Module.Flat.rTensor_exact M h
  rw [LinearMap.rTensor_smul_action, LinearMap.rTensor_smul_action] at ht
  let e := TensorProduct.lid R M
  intro x
  constructor
  · intro hx
    have hy : b • e.symm x = 0 := by
      apply e.injective
      rw [map_smul, e.apply_symm_apply, map_zero]
      exact hx
    obtain ⟨z, hz⟩ := (ht (e.symm x)).mp hy
    refine ⟨e z, ?_⟩
    change a • e z = x
    exact (e.map_smul a z).symm.trans ((congrArg e hz).trans (e.apply_symm_apply x))
  · rintro ⟨y, rfl⟩
    have hy := ht.apply_apply_eq_zero (e.symm y)
    change b • (a • e.symm y) = 0 at hy
    change b • (a • y) = 0
    simpa only [map_smul, e.apply_symm_apply, map_zero] using congrArg e hy

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlatScalarExactness
