import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFunction

/-! # Quotient Free Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientFreeBaseChange.GradedHilbert

noncomputable section

/-! Free homogeneous coordinate pieces and their ranks survive arbitrary
coefficient extensions to nonzero commutative rings. -/

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {n : ℕ}

theorem degreeQuotient_free_baseChange (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ)
    [Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] :
    Module.Free A (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d) :=
  Module.Free.of_equiv (Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := A) I d)

theorem degreeQuotient_finrank_baseChange_of_free_ring [Nontrivial A]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ)
    [Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  let : Nontrivial R := (algebraMap R A).domain_nontrivial
  change Module.finrank A (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d) = _
  rw [← (Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := A) I d).finrank_eq]
  exact Module.finrank_baseChange

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientFreeBaseChange.GradedHilbert
