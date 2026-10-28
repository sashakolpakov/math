import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolynomialSectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FramedEvaluationZero

/-! # Polynomial Coordinate Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolynomialCoordinateFrame

noncomputable section

/-! The selected coordinate power gives an actual frame after
pullback to a normalized affine projective point. Its value in any
other actual fiber frame is therefore a unit. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ}

def homogeneousCoordinatePower (i : Fin (n + 1)) (d : ℕ) : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d :=
  ⟨X i ^ d, by simpa only [smul_eq_mul, mul_one] using
    SetLike.pow_mem_graded d (show X i ∈ HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n 1 from isHomogeneous_X R i)⟩

theorem normalizedPolynomialCoordinate_isFrame
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) (hd : 0 < d)
    (x : Spec (.of R) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (v : Fin (n + 1) → R) (i : Fin (n + 1)) (hi : v i = 1)
    (hx : x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I = AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R v i hi) :
    IsIso (Ample.LineBundles.pullbackSection x (Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I d
      ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ (homogeneousCoordinatePower i d)))) := by
  apply (Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
  rw [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange x (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d), Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection_nonvanishing I d hd]
  change x ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i ^ d)) = ⊤
  rw [map_pow, Proj.basicOpen_pow _ _ _ hd,
    ← ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_singleton I i, ← Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i]
  change (x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) = ⊤
  rw [hx, AffineProjective.CoordinatePreimages.affineProjectiveCoordinateMap_preimage, hi, PrimeSpectrum.basicOpen_one]

theorem normalizedPolynomialCoordinate_framedValue_isUnit
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) (hd : 0 < d)
    (x : Spec (.of R) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (v : Fin (n + 1) → R) (i : Fin (n + 1)) (hi : v i = 1)
    (hx : x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I = AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R v i hi)
    (e : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).pullback x).sheaf ≅ Line.Bundles.structureModule (Spec (.of R))) :
    IsUnit (Affine.FramedSectionEvaluation.affineFramedSectionValue (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d) x e
      (Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I d
        ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ (homogeneousCoordinatePower i d)))) := by
  have := normalizedPolynomialCoordinate_isFrame I d hd x v i hi hx
  exact Affine.FramedEvaluationZero.affineFramedSectionValue_isUnit_of_frame _ _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolynomialCoordinateFrame
