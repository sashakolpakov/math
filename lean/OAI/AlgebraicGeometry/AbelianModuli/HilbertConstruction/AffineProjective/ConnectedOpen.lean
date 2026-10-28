import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.ConnectedOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.HomogeneousCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoMorphismProperty

/-! # Connected Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The connected-fiber open for every pointed smooth family with an actual projective presentation over a Noetherian affine base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem AffineProjective.ConnectedOpen.pointedSmoothAffineEmbedded_connected_open
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {X : Over (Spec (.of R))} [Smooth X.hom]
    (j : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion j.left]
    (x : Spec (.of R) ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _) :
    ∃ U : (Spec (.of R)).Opens, ∀ (T : Scheme.{u}) (c : T ⟶ Spec (.of R)),
      GeometricallyConnected (pullback.snd X.hom c) ↔ Set.range c ⊆ (U : Set (Spec (.of R))) := by
  let F := Closed.Families.FlatClosedFamily.ofEmbedding j
  let e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily F.homogeneousIdeal ≅ X :=
    F.homogeneousFamilyIso ≪≫ (Closed.Families.FlatClosedFamily.ofEmbeddingIso j).symm
  have : IsProper X.hom := by
    rw [← j.w]
    infer_instance
  have : IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading F.homogeneousIdeal)) :=
    (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@IsProper : MorphismProperty Scheme.{u}) e).mpr inferInstance
  have : Smooth (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading F.homogeneousIdeal)) :=
    (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@Smooth : MorphismProperty Scheme.{u}) e).mpr inferInstance
  have hs : (x ≫ e.inv.left) ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading F.homogeneousIdeal) = 𝟙 _ :=
    (Category.assoc _ _ _).trans ((congrArg (fun f => x ≫ f) e.inv.w).trans hx)
  obtain ⟨U, hU⟩ := ProjectiveCoordinate.ConnectedOpen.pointedProperSmoothProjectiveCoordinate_connected_open
    F.homogeneousIdeal (x ≫ e.inv.left) hs
  refine ⟨U, fun T c => ?_⟩
  exact (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@GeometricallyConnected : MorphismProperty Scheme.{u})
    ((Over.pullback c).mapIso e)).symm.trans (hU T c)

theorem AffineProjective.ConnectedOpen.overIso_composition_closed {S : Scheme.{u}} {X Y Z : Over S}
    (j : X ⟶ Y) [IsClosedImmersion j.left] (e : Y ≅ Z) :
    IsClosedImmersion (j ≫ e.hom).left := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  exact inferInstanceAs (IsClosedImmersion (j.left ≫ e.hom.left))

def Projective.ProjectivePresentations.ProjectivePresentation.affineEmbedding
    {R : Type u} [CommRing R] {X : Over (Spec (.of R))} (P : Projective.ProjectivePresentations.ProjectivePresentation X) :
    X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R P.dimension :=
  P.embedding ≫ (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) P.dimension).hom

instance Projective.ProjectivePresentations.ProjectivePresentation.affineEmbedding_closed
    {R : Type u} [CommRing R] {X : Over (Spec (.of R))} (P : Projective.ProjectivePresentations.ProjectivePresentation X) :
    IsClosedImmersion P.affineEmbedding.left :=
  AffineProjective.ConnectedOpen.overIso_composition_closed P.embedding (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) P.dimension)

theorem AffineProjective.ConnectedOpen.pointedSmoothAffineProjective_connected_open
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Over (Spec (.of R))} [Smooth X.hom] (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (x : Spec (.of R) ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _) :
    ∃ U : (Spec (.of R)).Opens, ∀ (T : Scheme.{u}) (c : T ⟶ Spec (.of R)),
      GeometricallyConnected (pullback.snd X.hom c) ↔ Set.range c ⊆ (U : Set (Spec (.of R))) := by
  exact AffineProjective.ConnectedOpen.pointedSmoothAffineEmbedded_connected_open P.affineEmbedding x hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
