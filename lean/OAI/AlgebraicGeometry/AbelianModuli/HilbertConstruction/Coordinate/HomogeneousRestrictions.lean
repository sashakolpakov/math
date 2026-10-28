import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousChartFractions

/-! # Homogeneous Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousRestrictions

noncomputable section

/-! Homogeneous-localization restriction maps agree with the actual module-chart restriction maps under the coordinate equivalence. -/

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateHomogeneousRestriction {s t : Finset (Fin (n + 1))} (h : s ⊆ t) :
    HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
      (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)) →+*
    HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
      (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R t)) :=
  HomogeneousLocalization.awayMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
    (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I (t \ s))
    (by rw [← map_mul, HilbertScheme.Presentations.LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h])

theorem coordinateChartModuleEquiv_restriction {s t : Finset (Fin (n + 1))} (h : s ⊆ t)
    (z : HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
      (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))) :
    (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartModuleEquiv I t (coordinateHomogeneousRestriction I h z)).val =
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartModuleEquiv I s z).val := by
  obtain ⟨k, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
    (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I s) z
  apply (HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R t)).injective
  rw [HomogeneousChartFractions.coordinateChartModuleEquiv_value, HomogeneousChartFractions.coordinateChartModuleEquiv_fraction,
    HilbertScheme.Presentations.Module.ChartCompatibility.ProjectiveCech.moduleChartRestriction_fraction, HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv_fraction]
  simp only [coordinateHomogeneousRestriction, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]
  have hn : b * (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s))) ^ k = HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k • b :=
    (mul_comm _ _).trans
      ((congrArg (fun a : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal => a * b)
        (map_pow (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal))
          (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s)) k).symm).trans (Algebra.smul_def _ b).symm)
  exact congrArg (fun a : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal => Localization.mk a
    (HilbertScheme.Presentations.Module.Fractions.GradedModules.moduleDenominator (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R t)) k)) hn

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousRestrictions
