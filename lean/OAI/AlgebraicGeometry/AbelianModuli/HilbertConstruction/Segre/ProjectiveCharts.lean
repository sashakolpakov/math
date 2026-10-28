import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.HomogeneousRelations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ChartPresentation

/-! # Projective Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts

noncomputable section

/-! The actual homogeneous localization charts of the Segre equations are polynomial rings. -/

open _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective

universe u v w

variable (R : Type u) [CommRing R] {σ : Type v} {τ : Type w} (i : σ) (j : τ)

abbrev SegreHomogeneousChart :=
  HomogeneousLocalization.Away (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading (HomogeneousRelations.segreHomogeneousIdeal (σ := σ) (τ := τ) R))
    (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (HomogeneousRelations.segreHomogeneousIdeal R) (X (i, j)))

theorem segreAffineChartIdeal_eq :
    HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal (HomogeneousRelations.segreHomogeneousIdeal R) (i, j) = NormalizedCoordinates.segreNormalizedIdeal R i j :=
  (HomogeneousRelations.segreNormalizedIdeal_eq_sup R i j).symm

def segreHomogeneousChartEquiv : SegreHomogeneousChart R i j ≃ₐ[R] NormalizedCoordinates.SegreChartRing R i j :=
  (HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartPresentationAlgEquiv (HomogeneousRelations.segreHomogeneousIdeal R) (i, j)).symm.trans
    ((Ideal.quotientEquivAlgOfEq R (segreAffineChartIdeal_eq R i j)).trans
      (NormalizedQuotient.segreNormalizedChartEquiv R i j))

theorem segreHomogeneousChartEquiv_map (p : MvPolynomial (σ × τ) R) :
    segreHomogeneousChartEquiv R i j (HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (HomogeneousRelations.segreHomogeneousIdeal R) (i, j) p) =
      NormalizedCoordinates.segreChartEvaluation R i j p := by
  change NormalizedQuotient.segreNormalizedChartEquiv R i j
    (Ideal.quotientEquivAlgOfEq R (segreAffineChartIdeal_eq R i j)
      ((HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartPresentationAlgEquiv (HomogeneousRelations.segreHomogeneousIdeal R) (i, j)).symm
        (HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (HomogeneousRelations.segreHomogeneousIdeal R) (i, j) p))) = _
  rw [HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartPresentationAlgEquiv_symm_map, Ideal.quotientEquivAlgOfEq_mk]
  rfl

theorem segreHomogeneousChartEquiv_variable (a : σ) (b : τ) :
    segreHomogeneousChartEquiv R i j
      (HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (HomogeneousRelations.segreHomogeneousIdeal R) (i, j) (X (a, b))) =
        NormalizedCoordinates.segreRowCoordinate R i j a * NormalizedCoordinates.segreColumnCoordinate R i j b := by
  rw [segreHomogeneousChartEquiv_map, NormalizedCoordinates.segreChartEvaluation, aeval_X]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts
