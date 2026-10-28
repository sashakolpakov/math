import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramModel
import Mathlib.RingTheory.Noetherian.Basic

/-! # Model Noetherian Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! The finite coefficient rings of a closed diagram model remain noetherian. -/

open _root_.CategoryTheory

universe u v w

theorem AlgebraDiagramModel.ClosedAlgebraDiagramModel.closingCoefficients_noetherian
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R] [IsNoetherianRing C]
    {J : Type v} [Category.{w} J] {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C}
    (M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) A B) : IsNoetherianRing M.closingCoefficients := by
  have : Algebra.FiniteType C M.coefficients :=
    (Subalgebra.fg_iff_finiteType M.coefficients).mp M.finiteType
  have : IsNoetherianRing M.coefficients := Algebra.FiniteType.isNoetherianRing C M.coefficients
  have : Algebra.FiniteType M.coefficients M.closingCoefficients :=
    (Subalgebra.fg_iff_finiteType M.closingCoefficients).mp M.closingFiniteType
  exact Algebra.FiniteType.isNoetherianRing M.coefficients M.closingCoefficients

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
