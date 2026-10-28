import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioRestrictions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.RestrictionCoordinates

/-! # Ratio Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioSections

noncomputable section

/-! Homogeneous coordinate ratios as actual regular functions on the projective chart, compatible with restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateRatioSection (s : Finset (Fin (n + 1))) (i j : Fin (n + 1)) (hi : i ∈ s) :
    Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) :=
  Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _ (HomogeneousRatios.coordinateHomogeneousRatio I s i j hi)

theorem coordinateRatioSection_self (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) :
    coordinateRatioSection I s i i hi = 1 := by
  unfold coordinateRatioSection
  rw [RatioCocycle.coordinateHomogeneousRatio_self]
  exact (Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _).hom.map_one

theorem coordinateRatioSection_comp (s : Finset (Fin (n + 1))) (i j k : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) :
    coordinateRatioSection I s i j hi * coordinateRatioSection I s j k hj =
      coordinateRatioSection I s i k hi := by
  exact ((Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _).hom.map_mul _ _).symm.trans
    (congrArg (Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _)
      (RatioCocycle.coordinateHomogeneousRatio_comp I s i j k hi hj))

theorem coordinateRatioSection_restriction {s t : Finset (Fin (n + 1))} (h : s ⊆ t)
    (i j : Fin (n + 1)) (hi : i ∈ s) :
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h)).op
      (coordinateRatioSection I s i j hi) = coordinateRatioSection I t i j (h hi) := by
  have he := ConcreteCategory.congr_hom (ProjectiveChart.RestrictionCoordinates.coordinateAwayToSection_restriction I h)
    (HomogeneousRatios.coordinateHomogeneousRatio I s i j hi)
  have hf := congrArg (Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
    (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R t)))
    (RatioRestrictions.coordinateHomogeneousRatio_restriction I h i j hi)
  exact he.symm.trans hf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioSections
