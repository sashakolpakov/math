import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartPointFunctionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ChartSectionVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionPullbackZero
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatePreimages

/-! # Polynomial Section Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolynomialSectionEvaluation

noncomputable section

/-! For a normalized coordinate representative of a point in an
embedded projective family, vanishing of the actual polynomial section
is exactly zero polynomial evaluation over the point's coefficient ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n d : ℕ}

theorem polynomialSection_pullback_zero_iff_normalized_evaluation
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d)
    (x : Spec (.of B) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (v : Fin (n + 1) → B) (i : Fin (n + 1)) (hi : v i = 1)
    (hx : x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I = AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) B v i hi) :
    Ample.LineBundles.pullbackSection x
      (Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p)) = 0 ↔
        MvPolynomial.eval₂Hom (algebraMap R B) v p.val = 0 := by
  let U := Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)
  have hv : ⊤ ≤ AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) B v i hi ⁻¹ᵁ U := by
    change ⊤ ≤ AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) B v i hi ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)
    rw [AffineProjective.CoordinatePreimages.affineProjectiveCoordinateMap_preimage, hi, PrimeSpectrum.basicOpen_one]
  have hc : ⊤ ≤ (x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) ⁻¹ᵁ U := by
    rw [hx]
    exact hv
  have hI : ⊤ ≤ x ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} := by
    rw [← Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i]
    exact hc
  have he := Single.ChartSectionVanishing.openFrame_pullbackSection_eq_zero_iff_single_chart (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d) x
    (ProjectiveTwisting.Bundle.projectiveTwistingCover I)
    (Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p)) (ULift.up i) hI
  erw [Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection_tuple] at he
  have hvalue : Open.SectionPullback.openSectionPullback x (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) ⊤ hI
      (Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I d
        (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p)) i) =
      (Scheme.ΓSpecIso (.of B)).inv (MvPolynomial.eval₂Hom (algebraMap R B) v p.val) := by
    calc
      _ = Open.SectionPullback.openSectionPullback (x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) U ⊤ hc
          (Homogeneous.PolynomialChartPullback.homogeneousPolynomialChartFunction p i) := Polynomial.SectionPullbackZero.polynomialChart_pullback_composite I p x i ⊤ hI hc
      _ = Open.SectionPullback.openSectionPullback (AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) B v i hi) U ⊤ hv
          (Homogeneous.PolynomialChartPullback.homogeneousPolynomialChartFunction p i) := Open.SectionPullbackComposition.openSectionPullback_congr hx U ⊤ hc hv _
      _ = _ := Affine.ChartPointFunctionValues.affineProjectiveCoordinateMap_polynomialValue v i hi hv p
  rw [he, hvalue]
  constructor
  · intro h
    apply (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm.injective
    exact h.trans (map_zero _).symm
  · intro h
    rw [h, map_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolynomialSectionEvaluation
