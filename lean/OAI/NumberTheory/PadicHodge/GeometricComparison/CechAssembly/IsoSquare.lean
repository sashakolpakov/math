import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Iso
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor

/-! # Iso Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.IsoSquare.CechAssemblyIsoSquare

noncomputable section

/-! An actual square of complex-valued diagrams remains a square
under the original assembled Cech isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a b
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  {P₁ P₂ Q₁ Q₂ : Cᵒᵖ ⥤ CochainComplex A ℕ}
  (e₁ : P₁ ≅ Q₁) (e₂ : P₂ ≅ Q₂) (a : P₂ ⟶ P₁) (b : Q₂ ⟶ Q₁)
  (h : a ≫ e₁.hom = e₂.hom ≫ b)

include h in
theorem naturality : (TotalFunctor.CechAssemblyTotalFunctor.functor E).map a ≫ (Iso.CechAssemblyIso.totalIso E e₁).hom =
    (Iso.CechAssemblyIso.totalIso E e₂).hom ≫ (TotalFunctor.CechAssemblyTotalFunctor.functor E).map b :=
  ((TotalFunctor.CechAssemblyTotalFunctor.functor E).map_comp a e₁.hom).symm.trans
    ((congrArg (TotalFunctor.CechAssemblyTotalFunctor.functor E).map h).trans
      ((TotalFunctor.CechAssemblyTotalFunctor.functor E).map_comp e₂.hom b))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.IsoSquare.CechAssemblyIsoSquare
