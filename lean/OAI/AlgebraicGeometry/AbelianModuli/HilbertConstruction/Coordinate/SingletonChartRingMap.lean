import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardChartRingMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioSections

/-! # Singleton Chart Ring Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.SingletonChartRingMap

noncomputable section

/-! The native quotient localization map on a singleton coordinate chart
sends a standard normalized coordinate to the actual homogeneous ratio
used by the twisting-bundle frames. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateSingletonDenominator_eq (i : Fin (n + 1)) :
    HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i) = HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}) :=
  congrArg (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) (HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton R i).symm

def coordinateSingletonChartRingMap (i : Fin (n + 1)) :
    ProjectiveChart.Evaluation.projectiveChartRing R n i →+*
      HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i})) :=
  (Segre.StandardChartRingMap.homogeneousAwayEquivOfEq (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (coordinateSingletonDenominator_eq I i)).toRingHom.comp
    (HomogeneousLocalization.Away.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i))

theorem coordinateSingletonChartRingMap_coordinate (i j : Fin (n + 1)) :
    coordinateSingletonChartRingMap I i (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (X j)) =
      HomogeneousRatios.coordinateHomogeneousRatio I {i} i j (Finset.mem_singleton_self i) := by
  have hden : HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}) ∈ HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I 1 := by
    have hh := HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I {i}
    simp only [Finset.card_singleton] at hh
    exact hh
  rw [HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize_X]
  change Segre.StandardChartRingMap.homogeneousAwayEquivOfEq (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (coordinateSingletonDenominator_eq I i)
    (HomogeneousLocalization.Away.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i)
      (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R i) 1 (X j)
        (by change (X j).IsHomogeneous (1 • 1); simpa only [one_smul] using isHomogeneous_X R j))) = _
  rw [HomogeneousLocalization.Away.map_mk,
    Segre.StandardChartRingMap.homogeneousAwayEquivOfEq_mk _ _ _ hden]
  unfold HomogeneousRatios.coordinateHomogeneousRatio Homogeneous.FactorRatios.homogeneousFactorRatio
  simp only [Finset.card_singleton, Finset.erase_singleton, HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech.inversionMonomial_empty, map_one, mul_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.SingletonChartRingMap
