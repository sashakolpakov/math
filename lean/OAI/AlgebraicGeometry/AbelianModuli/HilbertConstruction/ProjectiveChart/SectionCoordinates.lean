import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartCoefficientSections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces

/-! # Section Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.SectionCoordinates

noncomputable section

/-! Actual regular functions on each projective coordinate basic open are the corresponding degree-zero localized coordinate module, linearly over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateProjectiveChartOpen (s : Finset (Fin (n + 1))) : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens :=
  Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
    (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))

def coordinateProjectiveChartSectionEquiv (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (coordinateProjectiveChartOpen I s) ≃ₗ[R]
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0 := by
  let e := (Proj.basicOpenIsoSpec (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
    (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))
    (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I s) (Finset.card_pos.mpr hs)).symm
  have h : e.hom ≫ (coordinateProjectiveChartOpen I s).ι ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) =
      Spec.map (CommRingCat.ofHom (algebraMap R _)) :=
    (Category.assoc _ _ _).symm.trans
      (HilbertScheme.Presentations.Flat.ProjectiveCharts.GradedHilbert.projectiveStructureMap_away_homogeneous (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (Finset.card_pos.mpr hs)
        (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I s))
  exact (Affine.ChartCoefficientSections.affineChartCoefficientAlgEquiv (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (coordinateProjectiveChartOpen I s) e h).toLinearEquiv.trans (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartModuleEquiv I s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.SectionCoordinates
