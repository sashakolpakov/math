import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! # Eigenvalue Of Operator -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EigenvalueOfOperator

noncomputable section

/-! A monic integral annihilator of an operator annihilates each
of its eigenvalues. -/

theorem integral_eigenvalue_of_integral_operator
    {L : Type*} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (F : Module.End L V) (hF : IsIntegral ℤ F)
    (α : L) (hα : F.HasEigenvalue α) : IsIntegral ℤ α := by
  obtain ⟨Q, hQ, hFQ⟩ := hF
  have hmap : Polynomial.aeval F (Q.map (algebraMap ℤ L)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]
    exact hFQ
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have h := Module.End.aeval_apply_of_hasEigenvector (p := Q.map (algebraMap ℤ L)) hv
  rw [hmap, LinearMap.zero_apply] at h
  have hroot := (smul_eq_zero.mp h.symm).resolve_right hv.2
  exact ⟨Q, hQ, by
    simpa only [Polynomial.eval_map_algebraMap, Polynomial.aeval_def] using hroot⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EigenvalueOfOperator
