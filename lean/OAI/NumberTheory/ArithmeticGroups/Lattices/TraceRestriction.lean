import Mathlib

/-! # Trace Restriction -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.TraceRestriction.Construction

noncomputable section

/-! Restricting scalars composes the trace of a linear endomorphism
with the trace of the coefficient field. -/

open scoped Classical
open _root_.Module

theorem linear_trace_restrictScalars
    {k K V : Type*} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [Module K V] [IsScalarTower k K V]
    [Module.Finite k K] [Module.Finite K V] (f : Module.End K V) :
    LinearMap.trace k V (f.restrictScalars k) = Algebra.trace k K (LinearMap.trace K V f) := by
  let bK := Module.finBasis k K
  let bV := Module.finBasis K V
  rw [LinearMap.trace_eq_matrix_trace k (bK.smulTower' bV),
    LinearMap.restrictScalars_toMatrix, LinearMap.trace_eq_matrix_trace K bV]
  simp only [Matrix.trace, Matrix.diag, Matrix.comp_apply, Matrix.map_apply, Fintype.sum_prod_type, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (Algebra.trace_eq_matrix_trace bK _).symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.TraceRestriction.Construction
