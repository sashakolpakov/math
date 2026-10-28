import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramGluedStructure

/-! # Diagram Pullback Glued Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackGluedNaturality

noncomputable section

/-! Glued Cartesian morphisms commute with the projections from the base-changed glued diagrams. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {C D : Type u} [CommRing C] [CommRing D]
variable {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J]
variable {F G : J ⥤ Over (Spec (.of C))} (q : F ⟶ G) (hq : q.Equifibered)
variable (c : Spec (.of D) ⟶ Spec (.of C))
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
variable [((G ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h).left]
variable [((F ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (F.map h).left)

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (G.map h).left)

local instance {i j : J} (h : i ⟶ j) :
    IsOpenImmersion (((F ⋙ Over.pullback c) ⋙ Over.forget (Spec (.of D))).map h) :=
  DiagramPullbackProjection.diagramPullback_open F c h

local instance {i j : J} (h : i ⟶ j) :
    IsOpenImmersion (((G ⋙ Over.pullback c) ⋙ Over.forget (Spec (.of D))).map h) :=
  DiagramPullbackProjection.diagramPullback_open G c h

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.pullback c).map h).left :=
  DiagramPullbackProjection.diagramPullback_open F c h

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.pullback c).map h).left :=
  DiagramPullbackProjection.diagramPullback_open G c h

local instance : (((F ⋙ Over.pullback c) ⋙ Over.forget (Spec (.of D))) ⋙ Scheme.forget).IsLocallyDirected :=
  DiagramPullbackProjection.diagramPullback_locallyDirected F c

local instance : (((G ⋙ Over.pullback c) ⋙ Over.forget (Spec (.of D))) ⋙ Scheme.forget).IsLocallyDirected :=
  DiagramPullbackProjection.diagramPullback_locallyDirected G c

theorem diagramPullbackGluedMap_natural :
    DiagramPullbackGluing.diagramPullbackGluedMap F c ≫ Closed.DiagramGluedStructure.equifiberedOverGluedMap q hq =
      Closed.DiagramGluedStructure.equifiberedOverGluedMap (Functor.whiskerRight q (Over.pullback c)) (hq.whiskerRight (Over.pullback c)) ≫
        DiagramPullbackGluing.diagramPullbackGluedMap G c := by
  apply colimit.hom_ext
  intro i
  unfold DiagramPullbackGluing.diagramPullbackGluedMap Closed.DiagramGluedStructure.equifiberedOverGluedMap
  conv_lhs =>
    rw [← Category.assoc, Cartesian.DiagramGluing.cartesianDiagramGluedMap_ι, Category.assoc, Cartesian.DiagramGluing.cartesianDiagramGluedMap_ι]
  conv_rhs =>
    rw [← Category.assoc, Cartesian.DiagramGluing.cartesianDiagramGluedMap_ι, Category.assoc, Cartesian.DiagramGluing.cartesianDiagramGluedMap_ι]
  let a : (G.obj i).left ⟶ colimit (G ⋙ Over.forget (Spec (.of C))) :=
    colimit.ι (G ⋙ Over.forget (Spec (.of C))) i
  let m : (F.obj i).left ⟶ (G.obj i).left := (q.app i).left
  let n : pullback (F.obj i).hom c ⟶ pullback (G.obj i).hom c :=
    ((Over.pullback c).map (q.app i)).left
  have hw : pullback.fst (F.obj i).hom c ≫ m = n ≫ pullback.fst (G.obj i).hom c :=
    (Projective.PresentationBaseChange.overPullback_map_isPullback (q.app i) c).w
  change pullback.fst (F.obj i).hom c ≫ (m ≫ a) = n ≫ (pullback.fst (G.obj i).hom c ≫ a)
  rw [← Category.assoc, ← Category.assoc, hw]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackGluedNaturality
