import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistGlobalTuples
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech

/-! # Sections Cech -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.SectionsCech

noncomputable section

/-! Actual global sections of the constructed degree-d projective twisting line bundle are the homogeneous degree-d coordinate Čech sections, linearly over the base ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveTwistingSectionsCechMap (d : ℕ) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
      (Bundle.projectiveTwistingBundle I d).sheaf →ₗ[R]
    HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) :=
  ((Projective.TwistTupleCoordinates.coordinateTwistTupleCechEquiv I d).toLinearMap.comp (Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I d)).codRestrict _
    (fun s => (Projective.TwistCechKernel.coordinateTwistTupleCechEquiv_kernel_iff I d _).mpr
      ((Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap_range I d _).mp ⟨s, rfl⟩))

theorem projectiveTwistingSectionsCechMap_bijective (d : ℕ) :
    Function.Bijective (projectiveTwistingSectionsCechMap I d) := by
  constructor
  · intro x y h
    exact Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap_injective I d
      ((Projective.TwistTupleCoordinates.coordinateTwistTupleCechEquiv I d).injective (congrArg Subtype.val h))
  · intro z
    let e := Projective.TwistTupleCoordinates.coordinateTwistTupleCechEquiv I d
    have hx : Projective.TwistCechKernel.CoordinateTwistCompatible I d (e.symm z.val) :=
      (Projective.TwistCechKernel.coordinateTwistTupleCechEquiv_kernel_iff I d _).mp
        ((congrArg (fun a => a ∈ (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
          (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 1).ker)
            (e.apply_symm_apply z.val)).mpr z.property)
    obtain ⟨s, hs⟩ := (Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap_range I d (e.symm z.val)).mpr hx
    exact ⟨s, Subtype.ext ((congrArg e hs).trans (e.apply_symm_apply z.val))⟩

def projectiveTwistingSectionsCechEquiv (d : ℕ) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
      (Bundle.projectiveTwistingBundle I d).sheaf ≃ₗ[R]
    HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) :=
  LinearEquiv.ofBijective (projectiveTwistingSectionsCechMap I d) (projectiveTwistingSectionsCechMap_bijective I d)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.SectionsCech
