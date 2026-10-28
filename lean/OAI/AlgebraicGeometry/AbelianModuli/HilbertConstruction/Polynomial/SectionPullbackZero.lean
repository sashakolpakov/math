import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PolynomialChartPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackSectionZero

/-! # Section Pullback Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionPullbackZero

noncomputable section

/-! Vanishing of an actual polynomial twisting section along a scheme
map depends only on the composite map to the ambient projective space.
The criterion uses zero regular functions on all standard subcharts. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n d : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d)
variable {S : Scheme.{u}} (x : S ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))

theorem polynomialChart_pullback_composite (i : Fin (n + 1)) (V : S.Opens)
    (hI : V ≤ x ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})
    (hV : V ≤ (x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) :
    Open.SectionPullback.openSectionPullback x (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) V hI
      (Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I d
        (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p)) i) =
      Open.SectionPullback.openSectionPullback (x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I)
        (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) V hV (Homogeneous.PolynomialChartPullback.homogeneousPolynomialChartFunction p i) := by
  rw [← Homogeneous.PolynomialChartPullback.projectiveQuotient_polynomial_chart_pullback I p i
    (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i).ge]
  exact Open.SectionPullbackComposition.openSectionPullback_comp x (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I)
    (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) V
    (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i).ge hI hV _

def AmbientPolynomialVanishesAlong (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) (y : S ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) : Prop :=
  ∀ (i : Fin (n + 1)) (V : S.Opens) (hV : V ≤ y ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)),
    Open.SectionPullback.openSectionPullback y (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) V hV
      (Homogeneous.PolynomialChartPullback.homogeneousPolynomialChartFunction p i) = 0

theorem polynomialSection_pullback_eq_zero_iff_ambient :
    Ample.LineBundles.pullbackSection x
      (Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p)) = 0 ↔
      AmbientPolynomialVanishesAlong p (x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) := by
  let s := Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p)
  have he := OpenFrame.PullbackSectionZero.openFrame_pullbackSection_eq_zero_iff (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d) x
    (ProjectiveTwisting.Bundle.projectiveTwistingCover I) s
  constructor
  · intro h i V hV
    have hc := he.mp h (ULift.up i)
    erw [Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection_tuple] at hc
    have hI : V ≤ x ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} := by
      rw [← Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i]
      exact hV
    rw [← polynomialChart_pullback_composite I p x i V hI hV]
    change S.presheaf.map (homOfLE hI).op
      (x.app (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) _) = 0
    rw [hc, map_zero]
  · intro h
    apply he.mpr
    intro i
    erw [Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection_tuple]
    let V := x ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}
    have hV : V ≤ (x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) ⁻¹ᵁ
        Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i.down) := by
      change x ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down} ≤ _
      rw [← Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i.down]
      exact le_rfl
    have hc := h i.down V hV
    rw [← polynomialChart_pullback_composite I p x i.down V le_rfl hV] at hc
    change S.presheaf.map (𝟙 (.op V))
      (x.app (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}) _) = 0 at hc
    simpa only [S.presheaf.map_id, CommRingCat.id_apply] using hc

theorem polynomialSection_pullback_zero_iff_of_ambient_eq
    (J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (y : S ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J))
    (hxy : x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I = y ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J) :
    Ample.LineBundles.pullbackSection x
      (Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p)) = 0 ↔
    Ample.LineBundles.pullbackSection y
      (Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection J d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d).mkQ p)) = 0 := by
  rw [polynomialSection_pullback_eq_zero_iff_ambient, polynomialSection_pullback_eq_zero_iff_ambient, hxy]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionPullbackZero
