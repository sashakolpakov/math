import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Iso
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.InverseSquare

/-! # Assembly Iso Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyIsoNaturality

noncomputable section

/-! Natural changes of diagram coordinates commute with the actual
assembled Čech total maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Simplicial

universe u v a b
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  {P Q P' Q' : Cᵒᵖ ⥤ CochainComplex A ℕ}
  (e : P ≅ P') (d : Q ≅ Q') (f : P ⟶ Q) (g : P' ⟶ Q')
  (h : f ≫ d.hom = e.hom ≫ g)

include h in
theorem inverse :
    (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map g ≫ (GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso E d.symm).hom =
    (GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso E e.symm).hom ≫ (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map f :=
  GeometricComparison.Functor.InverseSquare.FunctorInverseSquare.square (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E) e d f g h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyIsoNaturality
