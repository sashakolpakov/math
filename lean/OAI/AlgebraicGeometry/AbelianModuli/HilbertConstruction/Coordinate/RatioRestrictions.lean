import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioCocycle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousRestrictions

/-! # Ratio Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioRestrictions

noncomputable section

/-! Coordinate ratios commute with the actual homogeneous localization restriction maps. -/

open _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateLocalizationRestriction {s t : Finset (Fin (n + 1))} (h : s ⊆ t) :
    Localization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)) →+*
      Localization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R t)) :=
  Localization.awayLift (algebraMap _ _) _
    (IsLocalization.Away.isUnit_of_dvd (x := HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R t))
      ⟨HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s)), by rw [← map_mul, HilbertScheme.Presentations.LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h]⟩)

theorem coordinateLocalizationRestriction_algebraMap {s t : Finset (Fin (n + 1))} (h : s ⊆ t)
    (a : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) :
    coordinateLocalizationRestriction I h (algebraMap _ _ a) = algebraMap _ _ a := by
  unfold coordinateLocalizationRestriction
  exact IsLocalization.Away.lift_eq _ _ a

theorem coordinateHomogeneousRestriction_val {s t : Finset (Fin (n + 1))} (h : s ⊆ t)
    (z : HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))) :
    (HomogeneousRestrictions.coordinateHomogeneousRestriction I h z).val = coordinateLocalizationRestriction I h z.val :=
  HomogeneousLocalization.val_awayMap _ _ _ z

theorem coordinateHomogeneousRatio_restriction {s t : Finset (Fin (n + 1))} (h : s ⊆ t)
    (i j : Fin (n + 1)) (hi : i ∈ s) :
    HomogeneousRestrictions.coordinateHomogeneousRestriction I h (HomogeneousRatios.coordinateHomogeneousRatio I s i j hi) =
      HomogeneousRatios.coordinateHomogeneousRatio I t i j (h hi) := by
  apply HomogeneousLocalization.val_injective
  apply (HomogeneousRatios.coordinateChartVariable_isUnit I t i (h hi)).mul_left_cancel
  have he := congrArg (coordinateLocalizationRestriction I h) (HomogeneousRatios.coordinateHomogeneousRatio_mul I s i j hi)
  rw [map_mul, coordinateLocalizationRestriction_algebraMap, coordinateLocalizationRestriction_algebraMap] at he
  exact (congrArg (fun z => algebraMap _ (Localization.Away
      (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R t))) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) * z)
    (coordinateHomogeneousRestriction_val I h (HomogeneousRatios.coordinateHomogeneousRatio I s i j hi))).trans
      (he.trans (HomogeneousRatios.coordinateHomogeneousRatio_mul I t i j (h hi)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioRestrictions
