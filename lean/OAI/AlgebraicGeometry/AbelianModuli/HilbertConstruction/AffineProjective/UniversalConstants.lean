import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.UniversalConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectivePresentationConstants

/-! # Universal Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.UniversalConstants

noncomputable section

/-! Pointed proper smooth geometrically connected schemes with projective presentations over noetherian affine bases have only base global functions after every scheme base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem affineProjectivePresentation_baseChange_globalFunctions_isIso
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Over (Spec (.of R))} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (x : Spec (.of R) ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _)
    {T Y : Scheme.{u}} {a : Y ⟶ X.left} {b : Y ⟶ T} {c : T ⟶ Spec (.of R)}
    (H : IsPullback a b X.hom c) : IsIso b.appTop := by
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
  have hΓ := ProjectiveCoordinate.UniversalConstants.projectiveCoordinate_baseChange_globalFunctions_isIso F.homogeneousIdeal
    (x ≫ e.inv.left) he (IsPullback.of_hasPullback (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily F.homogeneousIdeal).hom c)
  have hΓ' : IsIso (pullback.snd X.hom c).appTop :=
    (HilbertConstruction.Over.IsoGlobalFunctions.overIso_appTop_isIso_iff ((Over.pullback c).mapIso e)).mp hΓ
  exact (Cartesian.GlobalFunctions.cartesian_globalFunctions_isIso_iff H).mpr hΓ'

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.UniversalConstants
