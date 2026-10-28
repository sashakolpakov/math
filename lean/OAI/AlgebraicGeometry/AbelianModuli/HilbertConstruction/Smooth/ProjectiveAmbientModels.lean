import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ModelAmbientBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AmbientGluedRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ModelNoetherianCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveModelExtension

/-! # Projective Ambient Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A closed affine diagram model produces a smooth projective scheme inside the actual base-changed original ambient gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {C R : Type u} [CommRing C] [CommRing R] [Algebra C R] [IsNoetherianRing C]
variable {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J] [Finite J]
variable (G : J ⥤ Over (Spec (.of C))) [∀ i, IsAffine (G.obj i).left]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
variable [((G ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
variable {B : Jᵒᵖ ⥤ CommAlgCat.{u} C} [∀ i, Algebra.Smooth C (B.obj i)]
variable (M : Closed.AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) (Affine.CoordinateFunctor.affineCoordinateFunctor C G) B)

local instance Closed.AlgebraDiagramModel.ClosedAlgebraDiagramModel.smoothProjectiveAmbient_open_1 {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (G.map h).left)

theorem Closed.AlgebraDiagramModel.ClosedAlgebraDiagramModel.exists_smooth_projective_ambient_model
    (P : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (HilbertConstruction.Smooth.DiagramGluing.smoothDiagramGluedMap G)))
    (E : Subalgebra M.closingCoefficients R) (hE : E.FG) :
    ∃ D : Subalgebra M.closingCoefficients R, E ≤ D ∧ D.FG ∧
      ∃ Y : Over (Spec (.of D)), Smooth Y.hom ∧ IsNoetherian Y.left ∧
        Nonempty (Projective.ProjectivePresentations.ProjectivePresentation Y) ∧
        ∃ j : Y ⟶ M.ambientBaseChange D (Over.mk (HilbertConstruction.Smooth.DiagramGluing.smoothDiagramGluedMap G)),
          IsClosedImmersion j.left ∧ IsIso ((Over.pullback
            (Spec.map (CommRingCat.ofHom (R := D) (S := R) (algebraMap D R)))).map j) := by
  have : IsNoetherianRing M.closingCoefficients := M.closingCoefficients_noetherian
  have {i j : J} (h : i ⟶ j) : IsOpenImmersion (M.targetDiagram.map h).left := M.targetDiagram_open G h
  have : ((M.targetDiagram ⋙ Over.forget (Spec (.of M.closingCoefficients))) ⋙ Scheme.forget).IsLocallyDirected :=
    M.targetDiagram_locallyDirected G
  obtain ⟨D, hED, hD, Y, hs, hn, hp, j, hj, hr⟩ :=
    M.exists_smooth_projective_extension (M.targetGluedProjective G P) E hE
  let c : Spec (.of D) ⟶ Spec (.of M.closingCoefficients) :=
    Spec.map (CommRingCat.ofHom (R := M.closingCoefficients) (S := D) (algebraMap M.closingCoefficients D))
  let r : Spec (.of R) ⟶ Spec (.of D) :=
    Spec.map (CommRingCat.ofHom (R := D) (S := R) (algebraMap D R))
  let e := (Over.pullback c).mapIso (M.targetGluedBaseChangeIso G)
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

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
