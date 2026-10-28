import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientTotal

/-! # Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Iso.CechAssemblyIso

noncomputable section

/-! Isomorphisms of actual complex-valued diagrams induce the original Cech total isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v a b
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  {P Q : Cᵒᵖ ⥤ CochainComplex A ℕ} (e : P ≅ Q)

def bicomplexIso :
    CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P) ≅
    CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) Q) :=
  ((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).mapIso
    ((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).mapIso e)

def totalIso : CoefficientTotal.CechAssemblyCoefficientTotal.total E P ≅ CoefficientTotal.CechAssemblyCoefficientTotal.total E Q :=
  HomologicalComplex₂.total.mapIso (bicomplexIso E e) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Iso.CechAssemblyIso
