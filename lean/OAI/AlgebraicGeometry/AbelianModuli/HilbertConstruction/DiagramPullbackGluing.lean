import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramGlobalRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DiagramGluing

/-! # Diagram Pullback Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackGluing

noncomputable section

/-! Gluing a base-changed affine diagram gives the actual base change of the glued scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {C D : Type u} [CommRing C] [CommRing D]
variable {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J]
variable (F : J ⥤ Over (Spec (.of C))) (c : Spec (.of D) ⟶ Spec (.of C))
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h).left]
variable [((F ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]

local instance {i j : J} (h : i ⟶ j) :
    IsOpenImmersion ((F ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (F.map h).left)

local instance {i j : J} (h : i ⟶ j) :
    IsOpenImmersion (((F ⋙ Over.pullback c) ⋙ Over.forget (Spec (.of D))).map h) :=
  DiagramPullbackProjection.diagramPullback_open F c h

local instance :
    (((F ⋙ Over.pullback c) ⋙ Over.forget (Spec (.of D))) ⋙ Scheme.forget).IsLocallyDirected :=
  DiagramPullbackProjection.diagramPullback_locallyDirected F c

def diagramPullbackGluedMap :
    colimit ((F ⋙ Over.pullback c) ⋙ Over.forget (Spec (.of D))) ⟶
      colimit (F ⋙ Over.forget (Spec (.of C))) :=
  Cartesian.DiagramGluing.cartesianDiagramGluedMap _ _ (DiagramPullbackProjection.diagramPullbackProjection F c) (DiagramPullbackProjection.diagramPullbackProjection_equifibered F c)

theorem diagramPullbackGluedMap_isPullback :
    IsPullback (diagramPullbackGluedMap F c)
      (Smooth.DiagramGluing.smoothDiagramGluedMap (F ⋙ Over.pullback c)) (Smooth.DiagramGluing.smoothDiagramGluedMap F) c := by
  apply Cartesian.DiagramGlobalRecovery.cartesianDiagramGluedMap_base_isPullback _ _ (DiagramPullbackProjection.diagramPullbackProjection F c)
    (DiagramPullbackProjection.diagramPullbackProjection_equifibered F c)
  intro i
  have hnew := Smooth.DiagramGluing.smoothDiagramGluedMap_ι (F ⋙ Over.pullback c) i
  have hold := Smooth.DiagramGluing.smoothDiagramGluedMap_ι F i
  change IsPullback (pullback.fst (F.obj i).hom c) _ _ c
  rw [hnew, hold]
  exact IsPullback.of_hasPullback (F.obj i).hom c

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackGluing
