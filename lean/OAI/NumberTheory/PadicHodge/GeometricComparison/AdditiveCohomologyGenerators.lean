import OAI.NumberTheory.PadicHodge.GeometricComparison.AdditiveCohomologyFormula
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientPaste
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantForget

/-! # Additive Cohomology Generators -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AdditiveCohomologyGenerators.AdditiveSheafCohomology

noncomputable section

/-! Normalize the additive cohomology comparison by a fixed coefficient map, independent of the site. -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientCo.SheafCoefficientAdjunction OAI.NumberTheory.PadicHodge.GeometricComparison.IntegerSheaf.IntegerSheafEquivalence OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientUnit.ConstantCoefficientExtension

variable (R : Type 1) [Field R] [CharZero R]

abbrev forgetFieldCoefficients : ModuleCat.{1} R ⥤ AddCommGrpCat.{1} :=
  SheafCoefficientCo.SheafCoefficientAdjunction.restrictCoefficients R ⋙ forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}

def coefficientUnit : AddCommGrpCat.of (ULift.{1} ℤ) ⟶
    (forgetFieldCoefficients R).obj (ModuleCat.of R R) :=
  (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}).map (ConstantCoefficientPaste.ConstantCoefficientUnit.coefficientUnit R)

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C)

omit [CharZero R] in
theorem sourceMap_generator :
    toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{1} ℤ))) ≫ (AdditiveCohomologyFormula.AdditiveSheafCohomology.sourceMap R J).hom =
      (Functor.const Cᵒᵖ).map (coefficientUnit R) ≫
        whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R)))
          (forgetFieldCoefficients R) := by
  let G := forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}
  let P := (Functor.const Cᵒᵖ).obj (ModuleCat.of ℤ (ULift.{1} ℤ))
  let Q := (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{1} ℤ))
  have h := ConstantForget.ConstantForgetGenerators.inv_generator J G (ModuleCat.of ℤ (ULift.{1} ℤ))
  change 𝟙 _ ≫ toSheafify J Q ≫ (ConstantCoefficientUnit.ConstantCoefficientExtension.forgetConstantIso J).inv.hom =
    whiskerRight (toSheafify J P) G at h
  rw [Category.id_comp] at h
  change toSheafify J Q ≫ (ConstantCoefficientUnit.ConstantCoefficientExtension.forgetConstantIso J).inv.hom ≫
    whiskerRight (ConstantCoefficientPaste.ConstantCoefficientUnit.sheafUnit R J).hom G = _
  erw [← Category.assoc, h]
  erw [← whiskerRight_comp, ConstantCoefficientPaste.ConstantCoefficientUnit.generator]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AdditiveCohomologyGenerators.AdditiveSheafCohomology
