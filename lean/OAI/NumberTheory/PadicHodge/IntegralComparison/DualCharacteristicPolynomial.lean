import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.Dual

/-! # Dual Characteristic Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DualCharacteristicPolynomial

noncomputable section

/-! Characteristic polynomials of dual maps and intertwined operators. -/

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

theorem dual (f : Module.End R M) : f.dualMap.charpoly = f.charpoly := by
  let b := Module.Free.chooseBasis R M
  rw [← LinearMap.charpoly_toMatrix f b, ← LinearMap.charpoly_toMatrix f.dualMap b.dualBasis]
  simp only [LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.charpoly_transpose]

theorem of_intertwines (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N)
    (h : e.toLinearMap.comp f = g.comp e.toLinearMap) : f.charpoly = g.charpoly := by
  have he : e.conj f = g := by
    apply LinearMap.ext
    intro x
    change e (f (e.symm x)) = g x
    have hx := congrArg (fun t : M →ₗ[R] N => t (e.symm x)) h
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hx
  rw [← he, LinearEquiv.charpoly_conj]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DualCharacteristicPolynomial
