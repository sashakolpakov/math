import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedProjectiveIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange

/-! # Quotient Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.QuotientZero

noncomputable section

/-! The projective quotient by the zero homogeneous ideal is the actual standard projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

theorem extendedHomogeneousIdeal_zero {A : Type u} [CommRing A] [Algebra R A] :
    HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) = ⊥ := by
  apply HomogeneousIdeal.ext
  exact Ideal.map_bot

def quotientZeroGradedInverse : HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) →+*ᵍ HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n where
  __ := (RingEquiv.quotientBot (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)).toRingHom
  map_mem h := by
    obtain ⟨p, hp, rfl⟩ := h
    exact hp

theorem quotientZeroGraded_left_inverse :
    (quotientZeroGradedInverse R n).comp (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))) =
      GradedRingHom.id (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) := by
  apply GradedRingHom.ext
  intro p
  exact RingEquiv.quotientBot_mk p

theorem quotientZeroGraded_right_inverse :
    (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))).comp (quotientZeroGradedInverse R n) =
      GradedRingHom.id (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))) := by
  apply GradedRingHom.ext
  intro p
  exact (RingEquiv.quotientBot (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)).symm_apply_apply p

def projectiveQuotientZeroIso :
    Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)))) ≅
      ProjectivePresentations.affineProjectiveSpace R n :=
  Over.isoMk (GradedProjectiveIsomorphism.gradedProjectiveIso (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)))
    (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap ⊥) (quotientZeroGradedInverse R n)
    (quotientZeroGraded_right_inverse R n) (quotientZeroGraded_left_inverse R n)).symm (by
      change Proj.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))) _ ≫
        (Proj.toSpecZero (ProjectivePresentations.coordinateGrading R n) ≫
          Spec.map (CommRingCat.ofHom (ProjectivePresentations.degreeZeroConstants R n).toRingHom)) = _
      rw [SpaceReindex.degreeZeroConstants_eq_algebraMap]
      exact MapOverBase.projectiveMap_over_base _ _ (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))) _
        (fun _ => rfl))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.QuotientZero
