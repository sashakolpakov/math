import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionChartValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FractionBasicOpen

/-! # Section Homogeneous Fractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionHomogeneousFractions

noncomputable section

/-! The standard-chart coefficients of canonical twisting sections
are the usual homogeneous fractions, as actual regular functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomogeneousLocalization
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateQuotientNumerator (d : ℕ) (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) : HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I d :=
  ⟨(HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d q).val, by
    rw [← HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading_nat I d]
    exact (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d q).property⟩

theorem quotientSingletonCoordinate_degree_one (i : Fin (n + 1)) :
    HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}) ∈ HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I 1 := by
  have h := HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I {i}
  rw [Finset.card_singleton] at h
  exact h

def coordinateQuotientChartFraction (d : ℕ) (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) (i : Fin (n + 1)) :
    Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i})) :=
  Away.isLocalizationElem (quotientSingletonCoordinate_degree_one I i) (coordinateQuotientNumerator I d q).property

theorem coordinateQuotientChartFraction_crossMultiply (d : ℕ) (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)
    (i : Fin (n + 1)) :
    (coordinateQuotientChartFraction I d q i).val *
      algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (Localization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i})))
        (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i})) ^ d =
    algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) _ (coordinateQuotientNumerator I d q).val := by
  rw [coordinateQuotientChartFraction, Away.isLocalizationElem, Away.val_mk, pow_one,
    Localization.mk_eq_mk']
  simpa only [map_pow] using
    (IsLocalization.mk'_spec (Localization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i})))
      (coordinateQuotientNumerator I d q).val
      (⟨(HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i})) ^ d, ⟨d, rfl⟩⟩ :
        Submonoid.powers (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}))))

theorem coordinateQuotientTwistingSectionMap_chart_fraction (d : ℕ) (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)
    (i : Fin (n + 1)) :
    Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I d (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q) i =
      Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _ (coordinateQuotientChartFraction I d q i) := by
  apply SectionChartValues.coordinateSectionLocalization_injective I {i} ⟨i, Finset.mem_singleton_self i⟩
  have hz : Projective.SectionLocalization.coordinateSectionLocalization I {i} ⟨i, Finset.mem_singleton_self i⟩
      (Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _ (coordinateQuotientChartFraction I d q i)) =
        (coordinateQuotientChartFraction I d q i).val :=
    congrArg HomogeneousLocalization.val (Projective.SectionLocalization.coordinateSectionHomogeneousEquiv_away I {i}
      ⟨i, Finset.mem_singleton_self i⟩ (coordinateQuotientChartFraction I d q i))
  refine Eq.trans ?_ hz.symm
  apply ((IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i})))
    (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}))).pow d).mul_right_cancel
  have h := SectionChartValues.coordinateQuotientTwistingSectionMap_chart_crossMultiply I d q i
  have hxi : HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i) = HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}) := by
    rw [HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton]
  rw [hxi] at h
  exact (mul_comm _ _).trans (h.trans (coordinateQuotientChartFraction_crossMultiply I d q i).symm)

theorem coordinateQuotientTwistingSectionMap_chart_basicOpen (d : ℕ) (hd : 0 < d)
    (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) (i : Fin (n + 1)) :
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).basicOpen
      (Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I d (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q) i) =
      ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (coordinateQuotientNumerator I d q).val := by
  rw [coordinateQuotientTwistingSectionMap_chart_fraction]
  exact Projective.FractionBasicOpen.projectiveFraction_basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (quotientSingletonCoordinate_degree_one I i)
    Nat.zero_lt_one (coordinateQuotientNumerator I d q).property hd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionHomogeneousFractions
