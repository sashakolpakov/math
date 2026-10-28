import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NestedNoetherianCoefficients

/-! # Model Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! All coefficient stages of a recovered closed model lie in one finitely generated noetherian subalgebra of the original ring. -/

open _root_.CategoryTheory

universe u v w

theorem AlgebraDiagramModel.ClosedAlgebraDiagramModel.finalCoefficients_finiteType
    {R : Type u} [CommRing R] (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C]
    {J : Type v} [Category.{w} J] {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C}
    (M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) A B) (D : Subalgebra M.closingCoefficients R) (hD : D.FG) :
    C ≤ D.restrictScalars ℤ ∧ Algebra.FiniteType ℤ D ∧ IsNoetherianRing D := by
  let : CommRing D := Subalgebra.toCommRing (R := M.closingCoefficients) (A := R) D
  obtain ⟨hC, hF, _⟩ := NestedNoetherianCoefficients.nested_noetherian_coefficients C M.coefficients M.closingCoefficients
    M.finiteType M.closingFiniteType
  have : Algebra.FiniteType ℤ M.closingCoefficients := hF
  have : Algebra.FiniteType M.closingCoefficients D := (Subalgebra.fg_iff_finiteType D).mp hD
  have : Algebra.FiniteType ℤ D :=
    Algebra.FiniteType.trans (S := M.closingCoefficients) hF
      (inferInstanceAs (Algebra.FiniteType M.closingCoefficients D))
  refine ⟨?_, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ D⟩
  intro r hr
  exact D.algebraMap_mem (⟨r, hC hr⟩ : M.closingCoefficients)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
