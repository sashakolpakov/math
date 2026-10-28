import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedLinearCoordinateIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex

/-! # Linear Coordinate Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LinearCoordinateIsomorphism

noncomputable section

/-! Invertible coordinate transformations act on HilbertConstruction's actual standard
projective space over a coefficient spectrum and over an arbitrary base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (n : ℕ)

def affineLinearCoordinateIso
    (e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R)) :
    Projective.ProjectivePresentations.affineProjectiveSpace R n ≅ Projective.ProjectivePresentations.affineProjectiveSpace R n :=
  Over.isoMk (GradedLinearCoordinateIsomorphism.linearCoordinateProjectiveIso e) (by
    change (GradedLinearCoordinateIsomorphism.linearCoordinateProjectiveIso e).hom ≫
      (AlgebraicGeometry.Proj.toSpecZero (Projective.ProjectivePresentations.coordinateGrading R n) ≫
        Spec.map (CommRingCat.ofHom (Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom)) = _
    rw [Projective.SpaceReindex.degreeZeroConstants_eq_algebraMap]
    exact Projective.MapOverBase.projectiveMap_over_base _ _ (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap)
      (GradedProjectiveIsomorphism.gradedMap_irrelevant_of_inverse _ _ _ _ (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap_inverse e))
      (fun r => (Linear.CoordinateSubstitution.polynomialLinearSubstitution e.symm.toLinearMap).commutes r))

def relativeLinearCoordinateIso (S : Scheme.{u})
    (e : (Fin (n + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) →₀ Γ(S, ⊤))) :
    Projective.ProjectivePresentations.projectiveSpaceOver S n ≅ Projective.ProjectivePresentations.projectiveSpaceOver S n :=
  (Over.pullback S.toSpecΓ).mapIso (affineLinearCoordinateIso n e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LinearCoordinateIsomorphism
