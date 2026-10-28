import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.DegreeSectionsEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.SectionsFinite

/-! # Eventual Projective Twist Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EventualProjectiveTwistSections

noncomputable section

/-! For each projective coordinate quotient over a noetherian ring, actual twisting-bundle sections agree with homogeneous coordinate degree pieces in all sufficiently large degrees. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateDegreeTwistingSectionsEquiv (d : ℕ)
    (h0 : HilbertScheme.Presentations.Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 0)
    (h1 : HilbertScheme.Presentations.Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 1) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d ≃ₗ[R]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
        (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf :=
  (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d).trans
    ((Cech.DegreeSectionsEquivalence.moduleCechDegreeSectionsEquiv (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) h0 h1).trans (ProjectiveTwisting.SectionsCech.projectiveTwistingSectionsCechEquiv I d).symm)

theorem projectiveTwistingSections_eventual_degree :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → Nonempty (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d ≃ₗ[R]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
        (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf) := by
  obtain ⟨B, hB⟩ := HilbertScheme.Presentations.Graded.CechVanishing.ProjectiveCech.moduleCech_eventual_exactness (σ := Fin (n + 1)) R
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
  refine ⟨B, fun d hd => ?_⟩
  have h : (B : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  exact ⟨coordinateDegreeTwistingSectionsEquiv I d (hB d h 0) (hB d h 1)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EventualProjectiveTwistSections
