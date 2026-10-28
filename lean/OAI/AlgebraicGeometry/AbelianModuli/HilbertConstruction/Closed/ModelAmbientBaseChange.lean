import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramModel
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Model Ambient Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! The actual ambient scheme after the three coefficient stages of a closed model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

abbrev AlgebraDiagramModel.ClosedAlgebraDiagramModel.ambientBaseChange
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {J : Type v} [Category.{w} J] {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C}
    (M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) A B) (D : Subalgebra M.closingCoefficients R)
    (X : Over (Spec (.of C))) : Over (Spec (.of D)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (R := M.closingCoefficients) (S := D)
    (algebraMap M.closingCoefficients D)))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap M.coefficients M.closingCoefficients)))).obj
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C M.coefficients)))).obj X))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
