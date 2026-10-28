import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces

/-! # Homogeneous Chart Fractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousChartFractions

noncomputable section

/-! The coordinate-chart module equivalence sends a homogeneous localization fraction to the same actual localized module fraction. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateChartModuleEquiv_value (s : Finset (Fin (n + 1)))
    (z : HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
      (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))) :
    HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)
      (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartModuleEquiv I s z).val = HomogeneousLocalization.val z :=
  LinearEquiv.apply_symm_apply _ _

theorem coordinateChartModuleEquiv_fraction (s : Finset (Fin (n + 1))) (k : ℕ)
    (b : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (hb : b ∈ HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I (k • s.card)) :
    (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartModuleEquiv I s (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
      (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I s) k b hb)).val =
      HilbertScheme.Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s) k b := by
  apply (HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)).injective
  change (HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))
    ((HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)).symm
      (HomogeneousLocalization.val (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
        (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I s) k b hb))) = _
  rw [LinearEquiv.apply_symm_apply, HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv_fraction]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousChartFractions
