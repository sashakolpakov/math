import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramGluing
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Equifibered Over Diagrams -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquifiberedOverDiagrams

noncomputable section

/-! Cartesian transformations over a base preserve open chart arrows and locally directed gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {S : Scheme.{u}} {J : Type v} [Category J]
variable {F G : J ⥤ Over S} (q : F ⟶ G) (hq : q.Equifibered)

include hq

theorem equifiberedOverDiagram_forget :
    (Functor.whiskerRight q (Over.forget S)).Equifibered := hq.whiskerRight (Over.forget S)

theorem equifiberedOverDiagram_open
    [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left] {i j : J} (h : i ⟶ j) :
    IsOpenImmersion (F.map h).left :=
  MorphismProperty.of_isPullback ((equifiberedOverDiagram_forget q hq) h).flip
    (inferInstanceAs (IsOpenImmersion (G.map h).left))

theorem equifiberedOverDiagram_locallyDirected [Quiver.IsThin J]
    [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
    [((G ⋙ Over.forget S) ⋙ Scheme.forget).IsLocallyDirected] :
    ((F ⋙ Over.forget S) ⋙ Scheme.forget).IsLocallyDirected := by
  have {i j : J} (h : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget S).map h) :=
    equifiberedOverDiagram_open q hq h
  exact Scheme.isLocallyDirected_of_equifibered_of_injective
    (Functor.whiskerRight q (Over.forget S)) (equifiberedOverDiagram_forget q hq)
    (fun {_ _} h => ((F ⋙ Over.forget S).map h).isOpenEmbedding.injective)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquifiberedOverDiagrams
