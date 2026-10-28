import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness

/-! # Cech Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechCover

noncomputable section

/-! Projective coordinate opens form an affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveCechOpens (i : ULift.{u} (Fin (n + 1))) : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens :=
  (SectionCover.projectiveCoordinateSectionCover I).opens i.down

theorem projectiveCechOpens_affine (i : ULift.{u} (Fin (n + 1))) :
    IsAffineOpen (projectiveCechOpens I i) :=
  (SectionCover.projectiveCoordinateSectionCover I).affine i.down

theorem projectiveCechOpens_cover (x : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) :
    ∃ i, x ∈ projectiveCechOpens I i := by
  obtain ⟨i, hi⟩ := (SectionCover.projectiveCoordinateSectionCover I).covers x
  exact ⟨ULift.up i, hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechCover
