import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Iso

/-! # Assembly Inverse Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyInverseCoordinates

noncomputable section

/-! The actual inverse diagram isomorphism commutes with assembled
coefficient coordinates before geometric parameters are specialized. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem prepend {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {L M N : C} {P Q : D} (s : L ⟶ M) (t : M ⟶ N)
    (a : F.obj M ⟶ P) (b : P ⟶ Q) (c : F.obj N ⟶ Q)
    (h : a ≫ b = F.map t ≫ c) :
    (F.map s ≫ a) ≫ b = F.map (s ≫ t) ≫ c := by
  rw [Category.assoc, h, F.map_comp, Category.assoc]

universe u v a b d e
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I)
  {P Q : Cᵒᵖ ⥤ CochainComplex A ℕ} (e : P ≅ Q)

theorem inverse :
    (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE Q).hom ≫
      (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map
        (Functor.isoWhiskerRight e (F.mapHomologicalComplex (.up ℕ))).inv =
    (F.mapHomologicalComplex (.up ℕ)).map (GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso E e.symm).hom ≫
      (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE P).hom :=
  (GeometricComparison.CechAssembly.CoefficientNaturality.CechAssemblyCoefficientNaturality.natural F E hE e.inv).symm

theorem coordinates {L : CochainComplex A ℕ}
    (s : L ≅ GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total E Q) :
    (((F.mapHomologicalComplex (.up ℕ)).mapIso s) ≪≫
      GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE Q).hom ≫
      (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map
        (Functor.isoWhiskerRight e (F.mapHomologicalComplex (.up ℕ))).inv =
    (((F.mapHomologicalComplex (.up ℕ)).mapIso (s ≪≫ GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso E e.symm)) ≪≫
      GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE P).hom := by
  exact prepend (F.mapHomologicalComplex (.up ℕ)) s.hom (GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso E e.symm).hom
    (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE Q).hom
    ((GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map
      (Functor.isoWhiskerRight e (F.mapHomologicalComplex (.up ℕ))).inv)
    (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE P).hom (inverse F E hE e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyInverseCoordinates
