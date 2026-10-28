import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveGlobalFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoGlobalFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoMorphismProperty
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.HomogeneousCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange

/-! # Projective Presentation Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectivePresentationConstants

noncomputable section

/-! A pointed proper smooth geometrically connected scheme with a projective presentation over a noetherian local ring has exactly the base's global regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem localProjectivePresentation_globalFunctions_isIso
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Over (Spec (.of R))} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (x : Spec (.of R) ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _) :
    IsIso X.hom.appTop := by
  let j := P.embedding ≫ (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) P.dimension).hom
  have hj : IsClosedImmersion j.left :=
    @IsClosedImmersion.comp _ _ _ P.embedding.left (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) P.dimension).hom.left
      P.closedImmersion (Grassmann.ProjectivePresentation.overIso_closedImmersion _)
  let F := Closed.Families.FlatClosedFamily.ofEmbedding j
  let e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily F.homogeneousIdeal ≅ X :=
    F.homogeneousFamilyIso ≪≫ (Closed.Families.FlatClosedFamily.ofEmbeddingIso j).symm
  have hp : IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading F.homogeneousIdeal)) :=
    (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@IsProper) e).mpr inferInstance
  have hs : Smooth (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading F.homogeneousIdeal)) :=
    (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@Smooth) e).mpr inferInstance
  have hg : GeometricallyConnected (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading F.homogeneousIdeal)) :=
    (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@GeometricallyConnected) e).mpr inferInstance
  have he : (x ≫ e.inv.left) ≫ (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily F.homogeneousIdeal).hom = 𝟙 _ := by
    rw [Category.assoc, e.inv.w, hx]
  have H := ProjectiveGlobalFunctions.localPointedProjectiveCoordinate_globalFunctions_isIso F.homogeneousIdeal (x ≫ e.inv.left) he
  exact (HilbertConstruction.Over.IsoGlobalFunctions.overIso_appTop_isIso_iff e).mp H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectivePresentationConstants
