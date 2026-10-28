import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeOnePolynomialPresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MapOverBase
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange

/-! # Degree One Projective Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeOneProjectivePresentation

noncomputable section

/-! Degree-one algebra generators give an actual projective
presentation over the coefficient spectrum, with its structure map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option cleanup.letToHave false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] {n : ℕ}
variable (D : Fin (n + 1) → A) (hD : ∀ j, D j ∈ g 1)
variable (hgen : Algebra.adjoin R (Set.range D) = ⊤)

def degreeOneAffineProjectiveEmbedding :
    Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap g) ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n :=
  Over.homMk (DegreeOnePolynomialPresentation.degreeOneProjectiveEmbedding g D hD hgen) (by
    change Proj.map (DegreeOnePolynomialPresentation.degreeOnePolynomialPresentation g D hD) _ ≫
      (Proj.toSpecZero (Projective.ProjectivePresentations.coordinateGrading R n) ≫
        Spec.map (CommRingCat.ofHom (Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom)) = _
    rw [Projective.SpaceReindex.degreeZeroConstants_eq_algebraMap]
    exact Projective.MapOverBase.projectiveMap_over_base _ _ (DegreeOnePolynomialPresentation.degreeOnePolynomialPresentation g D hD) _
      (fun r => (MvPolynomial.aeval D).commutes r))

private def presentationEmbedding :
    Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap g) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n :=
  degreeOneAffineProjectiveEmbedding g D hD hgen ≫ (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv

private theorem iso_closedImmersion {X Y : Scheme.{u}} (e : X ≅ Y) :
    IsClosedImmersion e.hom := by
  infer_instance

private theorem degreeOneProjectivePresentation_closed :
    IsClosedImmersion (presentationEmbedding g D hD hgen).left := by
  change IsClosedImmersion
    (DegreeOnePolynomialPresentation.degreeOneProjectiveEmbedding g D hD hgen ≫
      (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv.left)
  exact @IsClosedImmersion.comp _ _ _
    (DegreeOnePolynomialPresentation.degreeOneProjectiveEmbedding g D hD hgen)
    (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv.left
    (DegreeOnePolynomialPresentation.degreeOneProjectiveEmbedding_closed g D hD hgen)
    (iso_closedImmersion
      ((Over.forget (Spec (.of R))).mapIso (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).symm))

def degreeOneProjectivePresentation : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap g)) where
  dimension := n
  embedding := presentationEmbedding g D hD hgen
  closedImmersion := degreeOneProjectivePresentation_closed g D hD hgen

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeOneProjectivePresentation
