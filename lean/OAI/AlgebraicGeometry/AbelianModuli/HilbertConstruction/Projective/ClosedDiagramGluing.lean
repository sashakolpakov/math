import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramGluedStructure
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramGluedIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterLoci

/-! # Closed Diagram Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ClosedDiagramGluing

noncomputable section

/-! Closed Cartesian chart models inherit projective presentations from the glued ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {C : Type u} [CommRing C] {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J]
variable {F G : J ⥤ Over (Spec (.of C))}
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
variable [((G ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h).left]
variable [((F ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (G.map h).left)

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (F.map h).left)

def projectiveDiagramOfIso (e : F ≅ G)
    (P : ProjectivePresentations.ProjectivePresentation (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap G))) :
    ProjectivePresentations.ProjectivePresentation (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap F)) :=
  P.ofSourceIso (DiagramGluedIsomorphisms.diagramGluedOverIso e)

def projectiveClosedDiagramGluing (q : F ⟶ G) (hq : q.Equifibered)
    [∀ i, IsClosedImmersion (q.app i).left]
    (P : ProjectivePresentations.ProjectivePresentation (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap G))) :
    ProjectivePresentations.ProjectivePresentation (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap F)) := by
  have : IsClosedImmersion (Closed.DiagramGluedStructure.equifiberedOverGluedMorphism q hq).left :=
    Closed.DiagramGluedStructure.equifiberedOverGluedMorphism_closed q hq
  exact P.ofClosedImmersion (Closed.DiagramGluedStructure.equifiberedOverGluedMorphism q hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ClosedDiagramGluing
