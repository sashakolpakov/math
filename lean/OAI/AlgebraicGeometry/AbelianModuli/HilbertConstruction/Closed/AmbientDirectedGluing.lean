import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramAmbientIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramPullbackProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquifiberedOverDiagrams

/-! # Ambient Directed Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! The target of a recovered closed model has the locally directed gluing inherited from the actual ambient charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem AlgebraDiagramModel.ClosedAlgebraDiagramModel.targetDiagram_locallyDirected
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {J : Type v} [Category J] [Quiver.IsThin J]
    (G : J ⥤ Over (Spec (.of C))) [∀ i, IsAffine (G.obj i).left]
    [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
    [((G ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
    {B : Jᵒᵖ ⥤ CommAlgCat.{u} C}
    (M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) (Affine.CoordinateFunctor.affineCoordinateFunctor C G) B) :
    ((M.targetDiagram ⋙ Over.forget (Spec (.of M.closingCoefficients))) ⋙ Scheme.forget).IsLocallyDirected := by
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
  let e := M.targetBaseChangeIso G
  exact EquifiberedOverDiagrams.equifiberedOverDiagram_locallyDirected e.hom (NatTrans.Equifibered.of_isIso e.hom)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
