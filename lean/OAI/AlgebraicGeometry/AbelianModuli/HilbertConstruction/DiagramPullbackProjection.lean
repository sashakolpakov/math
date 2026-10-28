import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ColimitDirectedCover

/-! # Diagram Pullback Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackProjection

noncomputable section

/-! The projection from a base-changed scheme diagram is Cartesian and preserves locally directed gluing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {S T : Scheme.{u}} {J : Type v} [Category J]
variable (F : J ⥤ Over S) (f : T ⟶ S)

def diagramPullbackProjection : (F ⋙ Over.pullback f) ⋙ Over.forget T ⟶ F ⋙ Over.forget S where
  app i := pullback.fst (F.obj i).hom f
  naturality _ _ h := (Projective.PresentationBaseChange.overPullback_map_isPullback (F.map h) f).w.symm

theorem diagramPullbackProjection_equifibered : (diagramPullbackProjection F f).Equifibered :=
  fun _ _ h => (Projective.PresentationBaseChange.overPullback_map_isPullback (F.map h) f).flip

theorem diagramPullback_open
    [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h).left] {i j : J} (h : i ⟶ j) :
    IsOpenImmersion (((F ⋙ Over.pullback f) ⋙ Over.forget T).map h) :=
  MorphismProperty.of_isPullback (Projective.PresentationBaseChange.overPullback_map_isPullback (F.map h) f) inferInstance

theorem diagramPullback_locallyDirected [Quiver.IsThin J]
    [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h).left]
    [((F ⋙ Over.forget S) ⋙ Scheme.forget).IsLocallyDirected] :
    (((F ⋙ Over.pullback f) ⋙ Over.forget T) ⋙ Scheme.forget).IsLocallyDirected := by
  have {i j : J} (h : i ⟶ j) : IsOpenImmersion (((F ⋙ Over.pullback f) ⋙ Over.forget T).map h) :=
    diagramPullback_open F f h
  exact Scheme.isLocallyDirected_of_equifibered_of_injective (diagramPullbackProjection F f)
    (diagramPullbackProjection_equifibered F f) (fun {_ _} h =>
      (((F ⋙ Over.pullback f) ⋙ Over.forget T).map h).isOpenEmbedding.injective)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackProjection
