import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAssemblyNatural
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientNaturality

/-! # Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientNaturality.CechAssemblyCoefficientNaturality

noncomputable section

/-! Coefficient change commutes naturally with the original assembled
Cech total maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v a b d e
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I)
  {P Q : Cᵒᵖ ⥤ CochainComplex A ℕ} (a : P ⟶ Q)

omit [HasProducts.{0} A] [HasCoproducts.{0} A] [HasProducts.{0} B] [HasCoproducts.{0} B] in
theorem assembly_inverse :
    ((ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves F).mapHomologicalComplex (.up ℕ)).map
      (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) a) ≫ (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F Q).inv =
    (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F P).inv ≫
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℕ))) :=
  IntegralComparison.InverseCoordinateHomology.inverse (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F P) (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F Q)
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℕ))))
    (((ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves F).mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) a))
    (ComplexAssemblyNatural.ComplexAssemblyCoefficientNaturality.natural F a)

omit [HasProducts.{0} A] [HasCoproducts.{0} A] in
theorem total_assembly :
    CechPresheaf.CoefficientNaturality.CechPresheafCoefficientNaturality.totalMap E
      (((ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves F).mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) a)) ≫
        CechPresheaf.CoefficientNaturality.CechPresheafCoefficientNaturality.totalMap E (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F Q).inv =
    CechPresheaf.CoefficientNaturality.CechPresheafCoefficientNaturality.totalMap E (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F P).inv ≫
      (TotalFunctor.CechAssemblyTotalFunctor.functor E).map (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℕ))) := by
  let T := (FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (assembly_inverse F a)).trans (T.map_comp _ _))

theorem natural : (F.mapHomologicalComplex (.up ℕ)).map ((TotalFunctor.CechAssemblyTotalFunctor.functor E).map a) ≫
    (CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE Q).hom =
    (CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE P).hom ≫
      (TotalFunctor.CechAssemblyTotalFunctor.functor E).map (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℕ))) :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _
    (CechPresheaf.CoefficientNaturality.CechPresheafCoefficientNaturality.total F E hE (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) a))
    (total_assembly F E a)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientNaturality.CechAssemblyCoefficientNaturality
