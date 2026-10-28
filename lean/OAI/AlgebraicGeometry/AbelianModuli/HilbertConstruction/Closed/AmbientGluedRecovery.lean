import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AmbientProjectiveGluing

/-! # Ambient Glued Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! The glued target of a closed affine model is the actual iterated base change of the original ambient gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
variable {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J]
variable (G : J ⥤ Over (Spec (.of C))) [∀ i, IsAffine (G.obj i).left]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
variable [((G ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
variable {B : Jᵒᵖ ⥤ CommAlgCat.{u} C}
variable (M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) (Affine.CoordinateFunctor.affineCoordinateFunctor C G) B)
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (M.targetDiagram.map h).left]
variable [((M.targetDiagram ⋙ Over.forget (Spec (.of M.closingCoefficients))) ⋙ Scheme.forget).IsLocallyDirected]

local instance AlgebraDiagramModel.ClosedAlgebraDiagramModel.closedAmbientRecovery_open_1 {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (G.map h).left)

local instance AlgebraDiagramModel.ClosedAlgebraDiagramModel.closedAmbientRecovery_open_2 {i j : J} (h : i ⟶ j) :
    IsOpenImmersion ((M.targetDiagram ⋙ Over.forget (Spec (.of M.closingCoefficients))).map h) :=
  inferInstanceAs (IsOpenImmersion (M.targetDiagram.map h).left)

def AlgebraDiagramModel.ClosedAlgebraDiagramModel.targetGluedBaseChangeIso :
    Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap M.targetDiagram) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap M.coefficients M.closingCoefficients)))).obj
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C M.coefficients)))).obj
            (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap G))) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap C M.coefficients))
  let d := Spec.map (CommRingCat.ofHom (algebraMap M.coefficients M.closingCoefficients))
  have {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.pullback c).map h).left :=
    Affine.FunctorBaseChange.affineFunctorBaseChange_open G c h
  have : (((G ⋙ Over.pullback c) ⋙ Over.forget (Spec (.of M.coefficients))) ⋙ Scheme.forget).IsLocallyDirected :=
    DiagramPullbackProjection.diagramPullback_locallyDirected G c
  have {i j : J} (h : i ⟶ j) : IsOpenImmersion (((G ⋙ Over.pullback c) ⋙ Over.pullback d).map h).left :=
    Affine.FunctorBaseChange.affineFunctorBaseChange_open (G ⋙ Over.pullback c) d h
  have : ((((G ⋙ Over.pullback c) ⋙ Over.pullback d) ⋙ Over.forget (Spec (.of M.closingCoefficients))) ⋙
      Scheme.forget).IsLocallyDirected := DiagramPullbackProjection.diagramPullback_locallyDirected (G ⋙ Over.pullback c) d
  exact DiagramGluedIsomorphisms.diagramGluedOverIso (M.targetBaseChangeIso G) ≪≫
    DiagramPullbackGluedIso.diagramPullbackGluedOverIso (G ⋙ Over.pullback c) d ≪≫
      (Over.pullback d).mapIso (DiagramPullbackGluedIso.diagramPullbackGluedOverIso G c)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
