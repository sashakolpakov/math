import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackGluedNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquifiberedGluedIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.PullbackRecoveredIso

/-! # Diagram Global Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramGlobalRecovery

noncomputable section

/-! Recovery isomorphisms on Cartesian charts imply an isomorphism of the actual base-changed global morphism. -/

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

theorem equifiberedOverGluedMorphism_pullback_isIso
    [∀ i, IsIso ((Over.pullback c).map (q.app i))] :
    IsIso ((Over.pullback c).map (DiagramGluedStructure.equifiberedOverGluedMorphism q hq)) := by
  let q' := Functor.whiskerRight q (Over.pullback c)
  have (i : J) : IsIso (q'.app i) := inferInstanceAs (IsIso ((Over.pullback c).map (q.app i)))
  have : IsIso q' := NatIso.isIso_of_isIso_app q'
  have hq' : q'.Equifibered := hq.whiskerRight (Over.pullback c)
  have : IsIso (DiagramGluedStructure.equifiberedOverGluedMorphism q' hq') :=
    EquifiberedGluedIsomorphism.equifiberedOverGluedMorphism_isIso q' hq'
  exact HilbertConstruction.Over.PullbackRecoveredIso.isIso_overPullback_map_of_recovered_iso (DiagramGluedStructure.equifiberedOverGluedMorphism q hq) c
    (DiagramPullbackGluing.diagramPullbackGluedMap F c) (DiagramPullbackGluing.diagramPullbackGluedMap G c)
    (DiagramPullbackGluing.diagramPullbackGluedMap_isPullback F c) (DiagramPullbackGluing.diagramPullbackGluedMap_isPullback G c)
    (DiagramGluedStructure.equifiberedOverGluedMorphism q' hq') (DiagramPullbackGluedNaturality.diagramPullbackGluedMap_natural q hq c).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramGlobalRecovery
