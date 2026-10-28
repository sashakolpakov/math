import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackGluing

/-! # Diagram Pullback Glued Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackGluedIso

noncomputable section

/-! Cartesian recovery of a glued base-changed diagram is an isomorphism in the category over the new base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {C D : Type u} [CommRing C] [CommRing D]
variable {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J]
variable (F : J ⥤ Over (Spec (.of C))) (c : Spec (.of D) ⟶ Spec (.of C))
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h).left]
variable [((F ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (F.map h).left)

local instance {i j : J} (h : i ⟶ j) :
    IsOpenImmersion (((F ⋙ Over.pullback c) ⋙ Over.forget (Spec (.of D))).map h) :=
  DiagramPullbackProjection.diagramPullback_open F c h

local instance :
    (((F ⋙ Over.pullback c) ⋙ Over.forget (Spec (.of D))) ⋙ Scheme.forget).IsLocallyDirected :=
  DiagramPullbackProjection.diagramPullback_locallyDirected F c

def diagramPullbackGluedOverIso :
    Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap (F ⋙ Over.pullback c)) ≅
      (Over.pullback c).obj (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap F)) :=
  Over.isoMk (DiagramPullbackGluing.diagramPullbackGluedMap_isPullback F c).isoPullback
    (DiagramPullbackGluing.diagramPullbackGluedMap_isPullback F c).isoPullback_hom_snd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackGluedIso
