import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramSchemeModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeTensorDiagramIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorDiagramIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagramOpenIso

/-! # Diagram Ambient Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! The target of a recovered closed diagram is the actual iterated base change of the ambient charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
variable {J : Type v} [Category.{w} J] (G : J ⥤ Over (Spec (.of C)))
variable [∀ i, IsAffine (G.obj i).left] {B : Jᵒᵖ ⥤ CommAlgCat.{u} C}
variable (M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) (Affine.CoordinateFunctor.affineCoordinateFunctor C G) B)

def AlgebraDiagramModel.ClosedAlgebraDiagramModel.targetBaseChangeIso : M.targetDiagram ≅
    (G ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C M.coefficients)))) ⋙
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients M.closingCoefficients))) :=
  SchemeTensorDiagramIso.algebraSchemeTensorDiagramIso M.coefficients M.closingCoefficients
    (Affine.CoordinateFunctor.affineCoordinateFunctor C G ⋙ AlgebraTensorFunctor.algebraTensorFunctor C M.coefficients) ≪≫
      Functor.isoWhiskerRight (Affine.TensorDiagramIso.affineTensorDiagramIso C M.coefficients G)
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients M.closingCoefficients))))

theorem AlgebraDiagramModel.ClosedAlgebraDiagramModel.targetDiagram_open [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
    {i j : J} (h : i ⟶ j) : IsOpenImmersion (M.targetDiagram.map h).left := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap C M.coefficients))
  let d := Spec.map (CommRingCat.ofHom (algebraMap M.coefficients M.closingCoefficients))
  have {i j : J} (f : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.pullback c).map f).left :=
    Affine.FunctorBaseChange.affineFunctorBaseChange_open G c f
  have {i j : J} (f : i ⟶ j) : IsOpenImmersion (((G ⋙ Over.pullback c) ⋙ Over.pullback d).map f).left :=
    Affine.FunctorBaseChange.affineFunctorBaseChange_open (G ⋙ Over.pullback c) d f
  exact HilbertConstruction.Over.DiagramOpenIso.overDiagram_open_of_iso (M.targetBaseChangeIso G) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
