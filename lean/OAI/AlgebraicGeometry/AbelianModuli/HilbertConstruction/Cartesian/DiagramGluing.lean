import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ColimitDirectedCover

/-! # Diagram Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramGluing

noncomputable section

/-! Cartesian maps between locally directed chart diagrams glue, with Cartesian recovery on each chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J]
variable (F G : J ⥤ Scheme.{u})
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h)]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h)]
variable [(F ⋙ Scheme.forget).IsLocallyDirected] [(G ⋙ Scheme.forget).IsLocallyDirected]
variable (q : F ⟶ G) (hq : q.Equifibered)

def cartesianDiagramRelativeGluing : (ColimitDirectedCover.colimitDiagramCover G).RelativeGluingData where
  functor := F
  natTrans := q
  equifibered := hq

def cartesianDiagramGluedMap : colimit F ⟶ colimit G :=
  (cartesianDiagramRelativeGluing F G q hq).toBase

theorem cartesianDiagramGluedMap_ι (i : J) :
    colimit.ι F i ≫ cartesianDiagramGluedMap F G q hq = q.app i ≫ colimit.ι G i :=
  (cartesianDiagramRelativeGluing F G q hq).ι_toBase i

theorem cartesianDiagramGluedMap_isPullback (i : J) :
    IsPullback (q.app i) (colimit.ι F i) (colimit.ι G i) (cartesianDiagramGluedMap F G q hq) :=
  (cartesianDiagramRelativeGluing F G q hq).isPullback_natTrans_ι_toBase i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramGluing
