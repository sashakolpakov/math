import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.PullbackFromCharts

/-! # Diagram Global Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramGlobalRecovery

noncomputable section

/-! Cartesian recovery over a common base glues from all charts to the whole scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J]
variable (F G : J ⥤ Scheme.{u})
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h)]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h)]
variable [(F ⋙ Scheme.forget).IsLocallyDirected] [(G ⋙ Scheme.forget).IsLocallyDirected]

theorem cartesianDiagramGluedMap_base_isPullback (q : F ⟶ G) (hq : q.Equifibered)
    {S T : Scheme.{u}} (p : colimit F ⟶ S) (f : colimit G ⟶ T) (b : S ⟶ T)
    (hbase : ∀ i, IsPullback (q.app i) (colimit.ι F i ≫ p) (colimit.ι G i ≫ f) b) :
    IsPullback (DiagramGluing.cartesianDiagramGluedMap F G q hq) p f b :=
  Global.PullbackFromCharts.scheme_isPullback_of_cartesian_charts _ p f b (ColimitDirectedCover.colimitDiagramCover G) F.obj q.app
    (colimit.ι F) (DiagramGluing.cartesianDiagramGluedMap_isPullback F G q hq) hbase

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramGlobalRecovery
