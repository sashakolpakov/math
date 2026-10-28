import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquifiberedOverDiagrams
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DiagramGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GluingClosedImmersion

/-! # Diagram Glued Structure -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramGluedStructure

noncomputable section

/-! Compatible Cartesian closed chart embeddings glue over the base as a closed immersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {C : Type u} [CommRing C] {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J]
variable {F G : J ⥤ Over (Spec (.of C))} (q : F ⟶ G) (hq : q.Equifibered)
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
variable [((G ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h).left]
variable [((F ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (G.map h).left)

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (F.map h).left)

abbrev equifiberedOverGluedMap : colimit (F ⋙ Over.forget (Spec (.of C))) ⟶
    colimit (G ⋙ Over.forget (Spec (.of C))) :=
  Cartesian.DiagramGluing.cartesianDiagramGluedMap _ _ (Functor.whiskerRight q (Over.forget _))
    (EquifiberedOverDiagrams.equifiberedOverDiagram_forget q hq)

theorem equifiberedOverGluedMap_over :
    equifiberedOverGluedMap q hq ≫ Smooth.DiagramGluing.smoothDiagramGluedMap G = Smooth.DiagramGluing.smoothDiagramGluedMap F := by
  apply colimit.hom_ext
  intro i
  rw [← Category.assoc, Cartesian.DiagramGluing.cartesianDiagramGluedMap_ι, Category.assoc,
    Smooth.DiagramGluing.smoothDiagramGluedMap_ι, Smooth.DiagramGluing.smoothDiagramGluedMap_ι]
  exact (q.app i).w

def equifiberedOverGluedMorphism :
    Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap F) ⟶ Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap G) :=
  Over.homMk (equifiberedOverGluedMap q hq) (equifiberedOverGluedMap_over q hq)

theorem equifiberedOverGluedMorphism_closed [∀ i, IsClosedImmersion (q.app i).left] :
    IsClosedImmersion (equifiberedOverGluedMorphism q hq).left := by
  let d := Cartesian.DiagramGluing.cartesianDiagramRelativeGluing (F ⋙ Over.forget (Spec (.of C)))
    (G ⋙ Over.forget (Spec (.of C))) (Functor.whiskerRight q (Over.forget _))
      (EquifiberedOverDiagrams.equifiberedOverDiagram_forget q hq)
  have (i : J) : IsClosedImmersion (d.natTrans.app i) :=
    inferInstanceAs (IsClosedImmersion (q.app i).left)
  exact Relative.GluingClosedImmersion.relativeGluing_toBase_closed _ d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramGluedStructure
