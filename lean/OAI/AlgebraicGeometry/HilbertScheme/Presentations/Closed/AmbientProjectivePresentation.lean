import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientRange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ProjectivePresentation

/-! # Ambient Projective Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! Projective presentations and the actual family subschemes are
compatible with inclusion in a closed ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y) [IsClosedImmersion j.left]

section

def Has.Core.ProjectivePresentation.precompose (B : Has.Core.ProjectivePresentation Y) : Has.Core.ProjectivePresentation X where
  dimension := B.dimension
  embedding := j.left ≫ B.embedding
  closed := @IsClosedImmersion.comp _ _ _ _ _ inferInstance B.closed
  over_base := (Category.assoc _ _ _).trans
    ((congrArg (fun f => j.left ≫ f) B.over_base).trans j.w)

def Has.Core.ProjectivePresentation.closedAmbientEmbedding (B : Has.Core.ProjectivePresentation X) :
    X ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S B.dimension :=
  Over.homMk B.embedding B.over_base

instance Has.Core.ProjectivePresentation.closedAmbientEmbedding_closed (B : Has.Core.ProjectivePresentation X) :
    IsClosedImmersion B.closedAmbientEmbedding.left := B.closed

theorem Has.Core.ProjectivePresentation.canonical_precompose (B : Has.Core.ProjectivePresentation X) :
    (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S B.dimension).precompose B.closedAmbientEmbedding = B := by
  cases B
  congr 1

end

namespace Closed.AmbientProjectivePresentation.Hilbert

variable {T : Over S} (F : Hilbert.Functor.Family X T)

def closedAmbientSubschemeIso : F.val.subscheme ≅ (Hilbert.ClosedAmbientMap.pushforwardFamily j F).val.subscheme := by
  let f : F.val.subscheme ⟶ Hilbert.Functor.ambient Y T := F.val.subschemeι ≫ Hilbert.ClosedAmbientMap.ambientEmbedding j T
  let : IsClosedImmersion f := inferInstance
  let e := asIso f.toImage
  exact e

@[reassoc] theorem closedAmbientSubschemeIso_hom_inclusion :
    (closedAmbientSubschemeIso j F).hom ≫ (Hilbert.ClosedAmbientMap.pushforwardFamily j F).val.subschemeι =
      F.val.subschemeι ≫ Hilbert.ClosedAmbientMap.ambientEmbedding j T :=
  Scheme.Hom.toImage_imageι _

theorem closedAmbientSubschemeIso_hom_projection :
    (closedAmbientSubschemeIso j F).hom ≫ Hilbert.Functor.familyProjection Y (Hilbert.ClosedAmbientMap.pushforwardFamily j F).val =
      Hilbert.Functor.familyProjection X F.val := by
  change (closedAmbientSubschemeIso j F).hom ≫
    ((Hilbert.ClosedAmbientMap.pushforwardFamily j F).val.subschemeι ≫ Hilbert.Functor.ambientProjection Y T) = _
  rw [← Category.assoc, closedAmbientSubschemeIso_hom_inclusion, Hilbert.ClosedAmbientMap.ambientEmbedding_familyProjection]

omit [IsClosedImmersion j.left] in
@[reassoc] theorem ambientEmbedding_second (T : Over S) :
    Hilbert.ClosedAmbientMap.ambientEmbedding j T ≫ (prod.snd : T ⨯ Y ⟶ Y).left =
      (prod.snd : T ⨯ X ⟶ X).left ≫ j.left := by
  change (prod.map (𝟙 T) j).left ≫ (prod.snd : T ⨯ Y ⟶ Y).left = _
  rw [← Over.comp_left, prod.map_snd]
  rfl

theorem closedAmbientSubschemeIso_hom_projective (B : Has.Core.ProjectivePresentation Y) :
    (closedAmbientSubschemeIso j F).hom ≫ (Hilbert.ClosedAmbientMap.pushforwardFamily j F).val.subschemeι ≫
      (prod.snd : T ⨯ Y ⟶ Y).left ≫ B.embedding =
    F.val.subschemeι ≫ (prod.snd : T ⨯ X ⟶ X).left ≫ (B.precompose j).embedding := by
  rw [closedAmbientSubschemeIso_hom_inclusion_assoc, ambientEmbedding_second_assoc]
  rfl

end Closed.AmbientProjectivePresentation.Hilbert

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
