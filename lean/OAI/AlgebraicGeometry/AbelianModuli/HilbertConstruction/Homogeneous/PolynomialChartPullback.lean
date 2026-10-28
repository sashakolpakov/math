import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CoordinatePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PolynomialSectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullbackComposition

/-! # Polynomial Chart Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PolynomialChartPullback

noncomputable section

/-! The chart coefficient of the actual section attached to a
homogeneous polynomial is the pullback of its ambient fraction f/X_i^d.
This is an equality of regular functions over any coefficient ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomogeneousLocalization
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n d : ℕ}

def homogeneousPolynomialChartFunction (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) (i : Fin (n + 1)) :
    Γ(Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n), Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) :=
  Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)
    (Away.isLocalizationElem (isHomogeneous_X R i) p.property)

theorem projectiveQuotient_polynomial_chart_pullback (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) (i : Fin (n + 1))
    (h : ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ≤
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) :
    Open.SectionPullback.openSectionPullback (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i))
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) h (homogeneousPolynomialChartFunction p i) =
        Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I d
          (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p)) i := by
  have hxi : X i ∈ HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n 1 := isHomogeneous_X R i
  have hv := ConcreteCategory.congr_hom
    (Proj.awayToSection_comp_appLE (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I) hxi)
    (Away.isLocalizationElem hxi p.property)
  let P (z : HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I 1) : Prop := ∀ hz : Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) z.val ≤
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i),
    Open.SectionPullback.openSectionPullback (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i))
      (Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) z.val) hz (homogeneousPolynomialChartFunction p i) =
        Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) z.val
          (Away.isLocalizationElem z.property ((HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem p.property))
  have hp : P ⟨HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i), (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem hxi⟩ := by
    intro hz
    simp only [ConcreteCategory.comp_apply] at hv
    change _ = Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
      (Away.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i) (Away.isLocalizationElem hxi p.property)) at hv
    simp only [Away.isLocalizationElem, Away.map_mk, map_pow] at hv
    exact hv
  have hz : (⟨HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}),
      Polynomial.SectionHomogeneousFractions.quotientSingletonCoordinate_degree_one I i⟩ : HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I 1) =
      ⟨HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i), (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem hxi⟩ := by
    apply Subtype.ext
    exact congrArg (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) (HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton R i)
  have hp' := (congrArg P hz).mpr hp
  rw [Polynomial.SectionHomogeneousFractions.coordinateQuotientTwistingSectionMap_chart_fraction]
  exact hp' h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PolynomialChartPullback
