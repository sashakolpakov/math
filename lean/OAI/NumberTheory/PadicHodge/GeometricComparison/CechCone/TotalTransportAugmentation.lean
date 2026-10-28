import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSourceNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport

/-! # Total Transport Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalTransportAugmentation.CechConeTotalTransportAugmentation

noncomputable section

/-! Canonical augmented Cech totals commute with additive coefficient
transport, including the original degree-zero source isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z w' z'
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) {Z : A} {Z' : B} (e : F.obj Z ≅ Z')
  (η : (Functor.const Cᵒᵖ).obj ((CochainComplex.single₀ A).obj Z) ⟶ P)

def cone : (Functor.const Cᵒᵖ).obj ((CochainComplex.single₀ B).obj Z') ⟶
    TotalCoefficient.CechConeTotalCoefficient.mapped F P :=
  (Functor.const Cᵒᵖ).map (IntegralComparison.Single.ComplexTransport.sourceIso F e).inv ≫
    TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone F P ((CochainComplex.single₀ A).obj Z) η

omit [HasBinaryProducts C] [HasProducts.{0} A] [HasCoproducts.{0} A]
  [HasProducts.{0} B] [HasCoproducts.{0} B] in
theorem cone_app (V : Cᵒᵖ) : (cone F P e η).app V = IntegralComparison.Single.ComplexTransport.map F e (η.app V) := by
  change (IntegralComparison.Single.ComplexTransport.sourceIso F e).inv ≫
    (TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone F P ((CochainComplex.single₀ A).obj Z) η).app V = _
  rw [TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone_app]
  rfl

theorem augmentation : IntegralComparison.Single.ComplexTransport.map F e
    (Total.CechConeTotal.augmentation U P ((CochainComplex.single₀ A).obj Z) η) ≫
      (TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).hom =
    Total.CechConeTotal.augmentation U (TotalCoefficient.CechConeTotalCoefficient.mapped F P)
      ((CochainComplex.single₀ B).obj Z') (cone F P e η) := by
  change ((IntegralComparison.Single.ComplexTransport.sourceIso F e).inv ≫ _) ≫ _ = _
  rw [Category.assoc, TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation]
  exact TotalSourceNaturality.CechConeTotalSourceNaturality.augmentation U _ _ _ _ (IntegralComparison.Single.ComplexTransport.sourceIso F e).inv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalTransportAugmentation.CechConeTotalTransportAugmentation
