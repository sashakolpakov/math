import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.DiagramEquifiberedDescent

/-! # Diagram Scheme Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! Closed algebra diagram models give smooth affine source charts and compatible closed embeddings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u v w

variable {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
variable {J : Type v} [Category.{w} J] {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C}
variable (M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) A B)

abbrev AlgebraDiagramModel.ClosedAlgebraDiagramModel.sourceDiagram : J ⥤ Over (Spec (.of M.closingCoefficients)) :=
  AlgebraSchemeDiagrams.algebraSchemeDiagram M.closingCoefficients
    ((B ⋙ AlgebraTensorFunctor.algebraTensorFunctor C M.coefficients) ⋙
      AlgebraTensorFunctor.algebraTensorFunctor M.coefficients M.closingCoefficients)

abbrev AlgebraDiagramModel.ClosedAlgebraDiagramModel.targetDiagram : J ⥤ Over (Spec (.of M.closingCoefficients)) :=
  AlgebraSchemeDiagrams.algebraSchemeDiagram M.closingCoefficients
    ((A ⋙ AlgebraTensorFunctor.algebraTensorFunctor C M.coefficients) ⋙
      AlgebraTensorFunctor.algebraTensorFunctor M.coefficients M.closingCoefficients)

abbrev AlgebraDiagramModel.ClosedAlgebraDiagramModel.schemeMap : M.sourceDiagram ⟶ M.targetDiagram :=
  AlgebraSchemeDiagrams.algebraSchemeDiagramMap M.closingCoefficients
    (Functor.whiskerRight M.map (AlgebraTensorFunctor.algebraTensorFunctor M.coefficients M.closingCoefficients))

instance AlgebraDiagramModel.ClosedAlgebraDiagramModel.schemeMap_closed (i : J) : IsClosedImmersion (M.schemeMap.app i).left := M.closed i

instance AlgebraDiagramModel.ClosedAlgebraDiagramModel.schemeMap_recovered (i : J) : IsIso ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap M.closingCoefficients R)))).map
      (M.schemeMap.app i)) := M.recovered i

instance AlgebraDiagramModel.ClosedAlgebraDiagramModel.sourceDiagram_smooth [∀ i, Algebra.Smooth C (B.obj i)] (i : J) :
    Smooth (M.sourceDiagram.obj i).hom := by
  have (j : Jᵒᵖ) : Algebra.Smooth M.closingCoefficients
      (((B ⋙ AlgebraTensorFunctor.algebraTensorFunctor C M.coefficients) ⋙
        AlgebraTensorFunctor.algebraTensorFunctor M.coefficients M.closingCoefficients).obj j) :=
    inferInstanceAs (Algebra.Smooth M.closingCoefficients
      (M.closingCoefficients ⊗[M.coefficients] (M.coefficients ⊗[C] B.obj j)))
  exact AlgebraSchemeDiagrams.algebraSchemeDiagram_smooth _ _ i

theorem AlgebraDiagramModel.ClosedAlgebraDiagramModel.exists_equifibered_extension [Finite J] [Quiver.IsThin J]
    [∀ i, Algebra.Smooth C (B.obj i)]
    [∀ {i j} (h : i ⟶ j), IsOpenImmersion (M.targetDiagram.map h).left]
    (E : Subalgebra M.closingCoefficients R) (hE : E.FG) :
    ∃ D : Subalgebra M.closingCoefficients R, E ≤ D ∧ D.FG ∧
      (Functor.whiskerRight M.schemeMap (Over.pullback
        (Spec.map (CommRingCat.ofHom (R := M.closingCoefficients) (S := D)
          (algebraMap M.closingCoefficients D))))).Equifibered :=
  Affine.DiagramEquifiberedDescent.exists_affine_diagram_equifibered_extension M.sourceDiagram M.targetDiagram M.schemeMap E hE

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
