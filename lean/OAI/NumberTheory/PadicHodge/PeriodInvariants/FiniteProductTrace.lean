import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.StdBasis

/-! # Finite Product Trace -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteProductTrace

noncomputable section

/-! # The canonical algebra trace on a finite product -/

open _root_.Module

variable (K : Type*) [CommRing K] {ι : Type*} [Fintype ι]
  (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
  {κ : ι → Type*} [∀ i, Fintype (κ i)]

theorem of_basis (b : ∀ i, Basis (κ i) K (B i)) (x : ∀ i, B i) :
    Algebra.trace K (∀ i, B i) x = ∑ i, Algebra.trace K (B i) (x i) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul,
    Pi.basis_repr, Pi.basis_apply, Pi.mul_apply, Pi.single_eq_same]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul] using
    (Algebra.trace_eq_matrix_trace (b i) (x i)).symm

theorem of_field (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
    [∀ i, FiniteDimensional K (B i)] (x : ∀ i, B i) :
    Algebra.trace K (∀ i, B i) x = ∑ i, Algebra.trace K (B i) (x i) :=
  of_basis K B (fun i => Module.finBasis K (B i)) x

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteProductTrace
