import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.RatioEquations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness

/-! # Homogeneous Ratios -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousRatios

noncomputable section

/-! Coordinate ratios on a multi-coordinate projective chart, with their defining multiplication equation. -/

open _root_.MvPolynomial DirectSum
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateRatioNumerator_homogeneous (s : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) (hi : i ∈ s) :
    HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X j) * HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i)) ∈
      HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I s.card := by
  have he : 1 + (s.erase i).card = s.card := by
    simpa only [Nat.add_comm] using Finset.card_erase_add_one hi
  rw [← he]
  exact SetLike.mul_mem_graded ((HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R j))
    (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I (s.erase i))

def coordinateHomogeneousRatio (s : Finset (Fin (n + 1))) (i j : Fin (n + 1)) (hi : i ∈ s) :
    HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)) :=
  Homogeneous.FactorRatios.homogeneousFactorRatio (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _ s.card (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I s)
    (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X j)) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i)))
    (coordinateRatioNumerator_homogeneous I s i j hi)

theorem coordinateHomogeneousRatio_mul (s : Finset (Fin (n + 1))) (i j : Fin (n + 1)) (hi : i ∈ s) :
    algebraMap _ (Localization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)))
      (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) * (coordinateHomogeneousRatio I s i j hi).val =
    algebraMap _ (Localization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)))
      (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X j)) := by
  apply Homogeneous.RatioEquations.homogeneousFactorRatio_mul
  rw [← map_mul, HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R s i hi]

theorem coordinateChartVariable_isUnit (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) :
    IsUnit (algebraMap _ (Localization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)))
      (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))) := by
  apply IsLocalization.Away.isUnit_of_dvd (x := HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))
  refine ⟨HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i)), ?_⟩
  rw [← map_mul, HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R s i hi]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousRatios
