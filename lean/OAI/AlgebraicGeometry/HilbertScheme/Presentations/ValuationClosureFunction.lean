import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedIdealLocalization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Valuation Closure Function -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFunction.GradedHilbert

noncomputable section

/-! All field fibers of a valuation-ring closure have exactly the same
Hilbert function as its original fraction-field fiber. -/

open scoped nonZeroDivisors

universe u v

theorem degreeQuotient_finrank_baseChange_of_free
    {R : Type u} [CommRing R] {L : Type v} [Field L] [Algebra R L] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) [Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := L) I).toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  let : Nontrivial R := (algebraMap R L).domain_nontrivial
  change Module.finrank L (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := L) I).toIdeal d) = _
  rw [← (Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := L) I d).finrank_eq]
  exact Module.finrank_baseChange

variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))

theorem valuationClosure_hilbertFunction_baseChange
    (L : Type v) [Field L] [Algebra R L] (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := L)
      (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I)).toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  let := ValuationClosureFlatness.GradedHilbert.valuationClosure_degree_free (R := R) I d
  have hK := degreeQuotient_finrank_baseChange_of_free (L := K) (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I) d
  rw [ContractedIdealLocalization.GradedHilbert.contractedHomogeneousIdeal_localization R⁰ I] at hK
  exact (degreeQuotient_finrank_baseChange_of_free (L := L) (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I) d).trans hK.symm

theorem valuationClosure_hasHilbertPolynomial_baseChange
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
    (L : Type v) [Field L] [Algebra R L] :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := L)
      (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I)).toIdeal P := by
  obtain ⟨N, hN⟩ := hP
  refine ⟨N, fun d hd => ?_⟩
  rw [valuationClosure_hilbertFunction_baseChange I L d]
  exact hN d hd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFunction.GradedHilbert
