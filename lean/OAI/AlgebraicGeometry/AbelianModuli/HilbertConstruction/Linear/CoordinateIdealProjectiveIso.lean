import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateIdeals
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SaturationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedProjectiveIsomorphism

/-! # Coordinate Ideal Projective Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateIdealProjectiveIso

noncomputable section

/-! Coordinate-transformed homogeneous ideals define genuinely
isomorphic projective families, with the precise ambient projective
coordinate map. No saturation or flatness hypothesis is needed. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {n : ℕ}
variable (e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R))
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def linearCoordinateIdealQuotientForward :
    HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (CoordinateIdeals.linearCoordinateIdeal e I) →+*ᵍ HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I where
  __ := Ideal.quotientMap I.toIdeal (CoordinateIdeals.polynomialLinearAlgEquiv e).toRingHom le_rfl
  map_mem h := by
    obtain ⟨p, hp, rfl⟩ := h
    exact ⟨CoordinateIdeals.polynomialLinearAlgEquiv e p, CoordinateSubstitution.polynomialLinearSubstitution_homogeneous _ hp, rfl⟩

def linearCoordinateIdealQuotientBackward :
    HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I →+*ᵍ HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (CoordinateIdeals.linearCoordinateIdeal e I) where
  __ := Ideal.quotientMap (CoordinateIdeals.linearCoordinateIdeal e I).toIdeal (CoordinateIdeals.polynomialLinearAlgEquiv e).symm.toRingHom (by
    intro p hp
    change CoordinateIdeals.polynomialLinearAlgEquiv e ((CoordinateIdeals.polynomialLinearAlgEquiv e).symm p) ∈ I.toIdeal
    rwa [AlgEquiv.apply_symm_apply])
  map_mem h := by
    obtain ⟨p, hp, rfl⟩ := h
    exact ⟨(CoordinateIdeals.polynomialLinearAlgEquiv e).symm p,
      CoordinateSubstitution.polynomialLinearSubstitution_homogeneous e.symm.toLinearMap hp, rfl⟩

theorem linearCoordinateIdealQuotient_forward_backward :
    (linearCoordinateIdealQuotientForward e I).comp (linearCoordinateIdealQuotientBackward e I) =
      GradedRingHom.id (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) := by
  apply GradedRingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mk I.toIdeal
    (CoordinateIdeals.polynomialLinearAlgEquiv e ((CoordinateIdeals.polynomialLinearAlgEquiv e).symm p)) = Ideal.Quotient.mk I.toIdeal p
  rw [AlgEquiv.apply_symm_apply]

theorem linearCoordinateIdealQuotient_backward_forward :
    (linearCoordinateIdealQuotientBackward e I).comp (linearCoordinateIdealQuotientForward e I) =
      GradedRingHom.id (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (CoordinateIdeals.linearCoordinateIdeal e I)) := by
  apply GradedRingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mk (CoordinateIdeals.linearCoordinateIdeal e I).toIdeal
    ((CoordinateIdeals.polynomialLinearAlgEquiv e).symm (CoordinateIdeals.polynomialLinearAlgEquiv e p)) =
      Ideal.Quotient.mk (CoordinateIdeals.linearCoordinateIdeal e I).toIdeal p
  rw [AlgEquiv.symm_apply_apply]

def linearCoordinateIdealProjectiveIso :
    Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) ≅ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (CoordinateIdeals.linearCoordinateIdeal e I)) :=
  GradedProjectiveIsomorphism.gradedProjectiveIso _ _ (linearCoordinateIdealQuotientBackward e I)
    (linearCoordinateIdealQuotientForward e I) (linearCoordinateIdealQuotient_backward_forward e I)
    (linearCoordinateIdealQuotient_forward_backward e I)

theorem linearCoordinateIdealQuotientForward_commutes (r : R) :
    linearCoordinateIdealQuotientForward e I
      (algebraMap R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (CoordinateIdeals.linearCoordinateIdeal e I).toIdeal) r) =
      algebraMap R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) r := by
  change Ideal.Quotient.mk I.toIdeal (CoordinateIdeals.polynomialLinearAlgEquiv e (algebraMap R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) r)) =
    Ideal.Quotient.mk I.toIdeal (algebraMap R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) r)
  rw [AlgEquiv.commutes]

def linearCoordinateIdealFamilyIso :
    Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (CoordinateIdeals.linearCoordinateIdeal e I) :=
  Over.isoMk (linearCoordinateIdealProjectiveIso e I) (by
    exact Projective.MapOverBase.projectiveMap_over_base _ _ (linearCoordinateIdealQuotientForward e I)
      (GradedProjectiveIsomorphism.gradedMap_irrelevant_of_inverse _ _ _ _ (linearCoordinateIdealQuotient_forward_backward e I))
      (linearCoordinateIdealQuotientForward_commutes e I))

theorem linearCoordinateIdealProjectiveIso_ambient :
    (linearCoordinateIdealProjectiveIso e I).hom ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (CoordinateIdeals.linearCoordinateIdeal e I) =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ (GradedLinearCoordinateIsomorphism.linearCoordinateProjectiveIso e.symm).hom := by
  change Proj.map (linearCoordinateIdealQuotientForward e I) _ ≫
    Proj.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap (CoordinateIdeals.linearCoordinateIdeal e I)) _ =
      Proj.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) _ ≫ Proj.map (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.toLinearMap) _
  rw [← Proj.map_comp, ← Proj.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateIdealProjectiveIso
