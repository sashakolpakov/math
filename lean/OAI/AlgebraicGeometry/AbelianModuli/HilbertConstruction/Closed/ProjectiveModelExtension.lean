import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramSchemeModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveClosedGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.DiagramBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FunctorBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PullbackRecoveryIso

/-! # Projective Model Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! A recovered closed affine diagram yields a smooth projective closed model after one finite extension making the overlaps Cartesian. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
variable {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J] [Finite J]
variable {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C} [∀ i, Algebra.Smooth C (B.obj i)]
variable (M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) A B) [IsNoetherianRing M.closingCoefficients]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (M.targetDiagram.map h).left]
variable [((M.targetDiagram ⋙ Over.forget (Spec (.of M.closingCoefficients))) ⋙ Scheme.forget).IsLocallyDirected]

local instance AlgebraDiagramModel.ClosedAlgebraDiagramModel.closedProjectiveExtension_open_1 {i j : J} (h : i ⟶ j) :
    IsOpenImmersion ((M.targetDiagram ⋙ Over.forget (Spec (.of M.closingCoefficients))).map h) :=
  inferInstanceAs (IsOpenImmersion (M.targetDiagram.map h).left)

theorem AlgebraDiagramModel.ClosedAlgebraDiagramModel.exists_smooth_projective_extension
    (P : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (HilbertConstruction.Smooth.DiagramGluing.smoothDiagramGluedMap M.targetDiagram)))
    (E : Subalgebra M.closingCoefficients R) (hE : E.FG) :
    ∃ D : Subalgebra M.closingCoefficients R, E ≤ D ∧ D.FG ∧
      ∃ Y : Over (Spec (.of D)), Smooth Y.hom ∧ IsNoetherian Y.left ∧
        Nonempty (Projective.ProjectivePresentations.ProjectivePresentation Y) ∧
        ∃ j : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom
          (R := M.closingCoefficients) (S := D) (algebraMap M.closingCoefficients D)))).obj
            (Over.mk (HilbertConstruction.Smooth.DiagramGluing.smoothDiagramGluedMap M.targetDiagram)),
          IsClosedImmersion j.left ∧ IsIso ((Over.pullback
            (Spec.map (CommRingCat.ofHom (R := D) (S := R) (algebraMap D R)))).map j) := by
  obtain ⟨D, hED, hD, hd⟩ := M.exists_equifibered_extension E hE
  have : Algebra.FiniteType M.closingCoefficients D := (Subalgebra.fg_iff_finiteType D).mp hD
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing M.closingCoefficients D
  let c : Spec (.of D) ⟶ Spec (.of M.closingCoefficients) :=
    Spec.map (CommRingCat.ofHom (R := M.closingCoefficients) (S := D) (algebraMap M.closingCoefficients D))
  let r : Spec (.of R) ⟶ Spec (.of D) :=
    Spec.map (CommRingCat.ofHom (R := D) (S := R) (algebraMap D R))
  let F := M.sourceDiagram ⋙ Over.pullback c
  let G := M.targetDiagram ⋙ Over.pullback c
  let q : F ⟶ G := Functor.whiskerRight M.schemeMap (Over.pullback c)
  have hq : q.Equifibered := hd
  have {i j : J} (h : i ⟶ j) : IsOpenImmersion (G.map h).left :=
    Affine.FunctorBaseChange.affineFunctorBaseChange_open M.targetDiagram c h
  have : ((G ⋙ Over.forget (Spec (.of D))) ⋙ Scheme.forget).IsLocallyDirected :=
    DiagramPullbackProjection.diagramPullback_locallyDirected M.targetDiagram c
  have {i j : J} (h : i ⟶ j) : IsOpenImmersion (F.map h).left :=
    EquifiberedOverDiagrams.equifiberedOverDiagram_open q hq h
  have : ((F ⋙ Over.forget (Spec (.of D))) ⋙ Scheme.forget).IsLocallyDirected :=
    EquifiberedOverDiagrams.equifiberedOverDiagram_locallyDirected q hq
  have (i : J) : IsAffine (F.obj i).left := Affine.FunctorBaseChange.affineFunctorBaseChange_affine M.sourceDiagram c i
  have (i : J) : Smooth (F.obj i).hom := by
    have : Smooth (M.sourceDiagram.obj i).hom := M.sourceDiagram_smooth i
    change Smooth (pullback.snd (M.sourceDiagram.obj i).hom c)
    infer_instance
  have (i : J) : IsClosedImmersion (q.app i).left := Projective.PresentationBaseChange.overPullback_map_closed (M.schemeMap.app i) c
  have (i : J) : IsIso ((Over.pullback r).map (q.app i)) :=
    Iterated.PullbackRecoveryIso.isIso_coefficient_iterated_overPullback D (M.schemeMap.app i)
  obtain ⟨Y, hs, hn, hp, j, hj, hr⟩ := HilbertConstruction.Smooth.ProjectiveClosedGluing.exists_smooth_projective_closed_gluing q hq r
    (Projective.DiagramBaseChange.projectiveDiagramBaseChange M.targetDiagram c P)
  let e := DiagramPullbackGluedIso.diagramPullbackGluedOverIso M.targetDiagram c
  have : IsClosedImmersion j.left := hj
  have : IsClosedImmersion e.hom.left := Grassmann.ProjectivePresentation.overIso_closedImmersion e
  have : IsIso ((Over.pullback r).map j) := hr
  refine ⟨D, hED, hD, Y, hs, hn, hp, j ≫ e.hom, ?_, ?_⟩
  · change IsClosedImmersion (j.left ≫ e.hom.left)
    exact IsClosedImmersion.comp _ _
  · change IsIso ((Over.pullback r).map (j ≫ e.hom))
    rw [Functor.map_comp]
    infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
