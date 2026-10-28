import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioSections

/-! # Section Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionLocalization

noncomputable section

/-! Actual chart regular functions embed in the ordinary localized coordinate ring, with the same values as the degree-zero coordinate-module equivalence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateSectionHomogeneousEquiv (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) ≃+*
      HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
        (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)) :=
  (Proj.basicOpenIsoAway (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _ (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I s)
    (Finset.card_pos.mpr hs)).commRingCatIsoToRingEquiv.symm

theorem coordinateSectionHomogeneousEquiv_away (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (z : HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
      (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))) :
    coordinateSectionHomogeneousEquiv I s hs (Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _ z) = z :=
  RingEquiv.symm_apply_apply _ z

def coordinateSectionLocalization (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) →+*
      Localization.Away (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)) :=
  (algebraMap _ _).comp (coordinateSectionHomogeneousEquiv I s hs).toRingHom

theorem coordinateSectionLocalization_value (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (x : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I s hs x).val = coordinateSectionLocalization I s hs x := by
  obtain ⟨z, rfl⟩ := (coordinateSectionHomogeneousEquiv I s hs).symm.surjective x
  have he := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartSectionEquiv_canonical I s hs z
  have hf := Coordinate.HomogeneousChartFractions.coordinateChartModuleEquiv_value I s z
  exact (congrArg (fun a => HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R)
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s) a.val) he).trans
      (hf.trans (congrArg HomogeneousLocalization.val
        (coordinateSectionHomogeneousEquiv_away I s hs z)).symm)

theorem coordinateSectionLocalization_ratio (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (i j : Fin (n + 1)) (hi : i ∈ s) :
    coordinateSectionLocalization I s hs (Coordinate.RatioSections.coordinateRatioSection I s i j hi) =
      (Coordinate.HomogeneousRatios.coordinateHomogeneousRatio I s i j hi).val :=
  congrArg HomogeneousLocalization.val (coordinateSectionHomogeneousEquiv_away I s hs _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionLocalization
