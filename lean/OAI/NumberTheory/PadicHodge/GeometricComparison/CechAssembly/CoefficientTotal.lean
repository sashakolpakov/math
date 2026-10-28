import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAssemblyPresheaves

/-! # Coefficient Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal

noncomputable section

/-! Coefficient change commutes with the original finite Cech total of
an assembled complex-valued diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v a b d e
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

def total : CochainComplex A ℕ :=
  (CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P)).total (.up ℕ)

def iso : (F.mapHomologicalComplex (.up ℕ)).obj (CechAssemblyCoefficientTotal.total E P) ≅
    CechAssemblyCoefficientTotal.total E (P ⋙ F.mapHomologicalComplex (.up ℕ)) :=
  CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P) ≪≫
    HomologicalComplex₂.total.mapIso
      (((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).mapIso
        (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F P).symm) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal
