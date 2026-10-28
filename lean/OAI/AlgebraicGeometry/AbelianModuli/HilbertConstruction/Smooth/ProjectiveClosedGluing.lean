import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramGlobalRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ClosedDiagramGluing

/-! # Projective Closed Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveClosedGluing

noncomputable section

/-! Smooth Cartesian closed charts with recovered isomorphisms give a smooth noetherian projective scheme and a recovered closed embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {C R : Type u} [CommRing C] [CommRing R] [IsNoetherianRing C]
variable {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J] [Finite J]
variable {F G : J ⥤ Over (Spec (.of C))}
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
variable [((G ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h).left]
variable [((F ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
variable [∀ i, IsAffine (F.obj i).left] [∀ i, Smooth (F.obj i).hom]

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (F.map h).left)

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (G.map h).left)

theorem exists_smooth_projective_closed_gluing
    (q : F ⟶ G) (hq : q.Equifibered) [∀ i, IsClosedImmersion (q.app i).left]
    (c : Spec (.of R) ⟶ Spec (.of C)) [∀ i, IsIso ((Over.pullback c).map (q.app i))]
    (P : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (DiagramGluing.smoothDiagramGluedMap G))) :
    ∃ Y : Over (Spec (.of C)), Smooth Y.hom ∧ IsNoetherian Y.left ∧
      Nonempty (Projective.ProjectivePresentations.ProjectivePresentation Y) ∧
      ∃ j : Y ⟶ Over.mk (DiagramGluing.smoothDiagramGluedMap G), IsClosedImmersion j.left ∧
        IsIso ((Over.pullback c).map j) := by
  refine ⟨Over.mk (DiagramGluing.smoothDiagramGluedMap F), ?_, DiagramGluing.smoothDiagramGlued_noetherian F,
    ⟨Projective.ClosedDiagramGluing.projectiveClosedDiagramGluing q hq P⟩, Closed.DiagramGluedStructure.equifiberedOverGluedMorphism q hq,
    Closed.DiagramGluedStructure.equifiberedOverGluedMorphism_closed q hq,
    Closed.DiagramGlobalRecovery.equifiberedOverGluedMorphism_pullback_isIso q hq c⟩
  exact DiagramGluing.smoothDiagramGluedMap_smooth F

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveClosedGluing
