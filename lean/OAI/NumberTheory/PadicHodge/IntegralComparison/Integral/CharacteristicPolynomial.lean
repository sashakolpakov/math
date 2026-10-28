import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EigenvalueOfOperator
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Characteristic Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CharacteristicPolynomial

noncomputable section

/-! Integrality of an operator forces integrality of every coefficient
of its characteristic polynomial. Rationality is a separate assertion. -/

open scoped TensorProduct

variable {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem coeff_integral_of_eigenvalues (f : Module.End K V)
    (h : ∀ α : AlgebraicClosure K,
      Module.End.HasEigenvalue (f.baseChange (AlgebraicClosure K)) α → IsIntegral ℤ α)
    (i : ℕ) : IsIntegral ℤ (f.charpoly.coeff i) := by
  let g := f.baseChange (AlgebraicClosure K)
  have hg : IsIntegral ℤ (g.charpoly.coeff i) := by
    apply Polynomial.isIntegral_coeff_of_factors
    · rw [(LinearMap.charpoly_monic g).leadingCoeff]
      exact isIntegral_one
    · exact IsAlgClosed.splits _
    · intro α hα
      exact h α ((Module.End.hasEigenvalue_iff_isRoot_charpoly g α).mpr hα)
  change IsIntegral ℤ ((f.baseChange (AlgebraicClosure K)).charpoly.coeff i) at hg
  rw [LinearMap.charpoly_baseChange, Polynomial.coeff_map] at hg
  exact isIntegral_algebraMap_iff.mp hg

theorem coeff_integral (f : Module.End K V) (hf : IsIntegral ℤ f) (i : ℕ) :
    IsIntegral ℤ (f.charpoly.coeff i) := by
  apply coeff_integral_of_eigenvalues f
  intro α hα
  exact GeometricComparison.Integral.EigenvalueOfOperator.integral_eigenvalue_of_integral_operator
    (f.baseChange (AlgebraicClosure K))
    (map_isIntegral_int (Module.End.baseChangeHom K (AlgebraicClosure K) V).toRingHom hf) α hα

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CharacteristicPolynomial
