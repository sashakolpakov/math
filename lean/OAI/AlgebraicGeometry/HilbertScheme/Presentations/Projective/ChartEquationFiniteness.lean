import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartFinitePresentation

/-! # Chart Equation Finiteness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartEquationFiniteness.GradedHilbert

noncomputable section

/-! Actual dehomogenized ideals of finitely presented projective families
are finitely generated over arbitrary coefficient rings. -/

open _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem projectiveQuotient_dehomogenizedIdeal_fg (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    [LocallyOfFinitePresentation (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))] (i : Fin (n + 1)) :
    (I.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i)).FG := by
  have h := (ChartFinitePresentation.GradedHilbert.projectiveQuotient_affineChartIdeal_fg I i).map (Dehomogenization.GradedHilbert.dehomogenize i)
  change ((I.toIdeal ⊔ Ideal.span {X i - 1}).map (Dehomogenization.GradedHilbert.dehomogenize i)).FG at h
  simpa only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_sub, Dehomogenization.GradedHilbert.dehomogenize_self,
    map_one, sub_self, Ideal.span_singleton_zero, sup_bot_eq] using h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartEquationFiniteness.GradedHilbert
