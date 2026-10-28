import Mathlib.LinearAlgebra.Trace

/-! # Eigenbasis Trace -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisTrace.Construction

noncomputable section

/-! The trace of an operator diagonal in a finite basis is the sum
of its eigenvalues, counted with their basis multiplicities. -/

open scoped Classical

theorem linear_trace_eq_sum_eigenvalues
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    (b : Module.Basis ι k V) (A : V →ₗ[k] V) (w : ι → k)
    (heig : ∀ i, A (b i) = w i • b i) : LinearMap.trace k V A = ∑ i, w i := by
  rw [LinearMap.trace_eq_matrix_trace k b]
  change (∑ i, LinearMap.toMatrix b b A i i) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply, heig]
  simp only [map_smul, Finsupp.smul_apply, b.repr_self_apply, ite_true, smul_eq_mul, mul_one]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisTrace.Construction
