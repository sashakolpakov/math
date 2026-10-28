import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Nonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness

/-! # Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Ampleness

noncomputable section

/-! The actual positive projective twisting bundles are ample over every coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveTwistingBundle_one_isAmple : (Bundle.projectiveTwistingBundle I 1).IsAmple := by
  have : IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) := HilbertScheme.Presentations.Projective.Properness.GradedHilbert.projectiveQuotient_proper I
  have : CompactSpace (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) :=
    QuasiCompact.compactSpace_of_compactSpace (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Bundle.projectiveTwistingCover I x
  refine ⟨1, Nat.zero_lt_one, Bundle.projectiveTwistingBundle I 1, Tensor.Powers.isTensorPower_one _,
    ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I i.down, ?_, ?_⟩
  · rw [ProjectiveCoordinate.Nonvanishing.projectiveCoordinateSection_nonvanishing]
    exact hi
  · rw [ProjectiveCoordinate.Nonvanishing.projectiveCoordinateSection_nonvanishing, ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_singleton]
    exact Proj.isAffineOpen_basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i.down))
      ((HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i.down)) Nat.zero_lt_one

theorem projectiveTwistingBundle_isAmple (d : ℕ) (hd : 0 < d) :
    (Bundle.projectiveTwistingBundle I d).IsAmple :=
  ((projectiveTwistingBundle_one_isAmple I).tensorPower d hd).of_iso
    (TensorPowers.projectiveTwistingBundle_tensorPowerIso I d)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Ampleness
