import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AmbientDirectedGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.DiagramBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ClosedDiagramGluing

/-! # Ambient Projective Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! The ambient target of a recovered closed diagram inherits an actual projective presentation. -/

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

local instance AlgebraDiagramModel.ClosedAlgebraDiagramModel.closedAmbientProjective_open_1 {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (G.map h).left)

local instance AlgebraDiagramModel.ClosedAlgebraDiagramModel.closedAmbientProjective_open_2 {i j : J} (h : i ⟶ j) :
    IsOpenImmersion ((M.targetDiagram ⋙ Over.forget (Spec (.of M.closingCoefficients))).map h) :=
  inferInstanceAs (IsOpenImmersion (M.targetDiagram.map h).left)

def AlgebraDiagramModel.ClosedAlgebraDiagramModel.targetGluedProjective (P : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap G))) :
    Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap M.targetDiagram)) := by
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
  exact Projective.ClosedDiagramGluing.projectiveDiagramOfIso (M.targetBaseChangeIso G)
    (Projective.DiagramBaseChange.projectiveDiagramBaseChange (G ⋙ Over.pullback c) d (Projective.DiagramBaseChange.projectiveDiagramBaseChange G c P))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
