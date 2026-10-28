import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Coordinates

/-! # Quotient Rank Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientRankBaseChange.GradedHilbert

noncomputable section

/-! Flat finite homogeneous quotients have the expected rank after any
coefficient extension, and equal dimensions over a field and its base residue field. -/

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {n : ℕ}

theorem degreeQuotient_rankAtStalk_baseChange (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ)
    [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d) p =
      Module.rankAtStalk (R := R) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) (p.comap (algebraMap R A)) :=
  (congrFun (Module.rankAtStalk_eq_of_equiv (Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := A) I d)) p).symm.trans
    (Module.rankAtStalk_baseChange p)

theorem degreeQuotient_field_hilbertFunction {K : Type v} [Field K] [Algebra R K]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I).toIdeal d =
      Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal
        (S := ((IsLocalRing.closedPoint K).comap (algebraMap R K)).asIdeal.ResidueField) I).toIdeal d := by
  have h := degreeQuotient_rankAtStalk_baseChange (A := K) I d (IsLocalRing.closedPoint K)
  rw [Module.rankAtStalk_eq_finrank_of_free, Relative.Coordinates.GradedHilbert.degreeQuotient_rankAtStalk] at h
  exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientRankBaseChange.GradedHilbert
