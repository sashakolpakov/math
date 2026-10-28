import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackGluedIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Diagram Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.DiagramBaseChange

noncomputable section

/-! Projective presentations survive gluing after a coefficient base change. -/

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

def projectiveDiagramBaseChange (P : ProjectivePresentations.ProjectivePresentation (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap F))) :
    ProjectivePresentations.ProjectivePresentation (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap (F ⋙ Over.pullback c))) :=
  (P.baseChange c).ofSourceIso (DiagramPullbackGluedIso.diagramPullbackGluedOverIso F c)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.DiagramBaseChange
