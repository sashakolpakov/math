import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousRestrictions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CanonicalChartSections

/-! # Restriction Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.RestrictionCoordinates

noncomputable section

/-! Actual regular-function restrictions between projective coordinate opens agree with coordinate Čech restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateProjectiveChartOpen_antitone {s t : Finset (Fin (n + 1))} (h : s ⊆ t) :
    SectionCoordinates.coordinateProjectiveChartOpen I t ≤ SectionCoordinates.coordinateProjectiveChartOpen I s := by
  apply Proj.basicOpen_mono
  refine ⟨algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s)), ?_⟩
  rw [← map_mul, HilbertScheme.Presentations.LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h]

theorem coordinateAwayToSection_restriction {s t : Finset (Fin (n + 1))} (h : s ⊆ t) :
    CommRingCat.ofHom (Coordinate.HomogeneousRestrictions.coordinateHomogeneousRestriction I h) ≫
      Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
        (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R t)) =
    Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
      (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)) ≫
      (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE (coordinateProjectiveChartOpen_antitone I h)).op :=
  Proj.awayMap_awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I (t \ s))
    (by rw [← map_mul, HilbertScheme.Presentations.LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h])

theorem coordinateProjectiveChartSectionEquiv_canonical (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (z : HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
      (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))) :
    SectionCoordinates.coordinateProjectiveChartSectionEquiv I s hs
      (Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
        (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)) z) =
      HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartModuleEquiv I s z :=
  congrArg (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartModuleEquiv I s)
    (Projective.CanonicalChartSections.projectiveAffineChartSectionsIso_awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
      (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I s) (Finset.card_pos.mpr hs) z)

theorem coordinateProjectiveChartSectionEquiv_restriction
    {s t : Finset (Fin (n + 1))} (hs : s.Nonempty) (ht : t.Nonempty) (h : s ⊆ t)
    (x : Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    (SectionCoordinates.coordinateProjectiveChartSectionEquiv I t ht
      ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE (coordinateProjectiveChartOpen_antitone I h)).op x)).val =
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h
        (SectionCoordinates.coordinateProjectiveChartSectionEquiv I s hs x).val := by
  have hsurj : Function.Surjective (Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
      (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))) :=
    (Proj.basicOpenIsoAway (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _ (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I s)
      (Finset.card_pos.mpr hs)).commRingCatIsoToRingEquiv.surjective
  obtain ⟨z, rfl⟩ := hsurj x
  have he := (ConcreteCategory.congr_hom (coordinateAwayToSection_restriction I h) z).symm
  exact (congrArg (fun y : Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (SectionCoordinates.coordinateProjectiveChartOpen I t) => (SectionCoordinates.coordinateProjectiveChartSectionEquiv I t ht y).val) he).trans
    ((congrArg Subtype.val (coordinateProjectiveChartSectionEquiv_canonical I t ht
      (Coordinate.HomogeneousRestrictions.coordinateHomogeneousRestriction I h z))).trans
      ((Coordinate.HomogeneousRestrictions.coordinateChartModuleEquiv_restriction I h z).trans
        (congrArg (fun y => HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h y.val)
          (coordinateProjectiveChartSectionEquiv_canonical I s hs z)).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.RestrictionCoordinates
