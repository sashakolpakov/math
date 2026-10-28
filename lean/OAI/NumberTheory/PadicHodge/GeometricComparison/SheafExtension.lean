import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientUnit

/-! # Sheaf Extension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafExtension.SheafExtensionGenerators

noncomputable section

/-! The constructed extension-of-coefficients isomorphism preserves sheafification generators. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientCo.SheafCoefficientAdjunction OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientUnit.ConstantCoefficientExtension

variable (R : Type 1) [Field R] [CharZero R]
  {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C)

omit [CharZero R] in
@[reassoc]
theorem extension_generator (P : Cᵒᵖ ⥤ ModuleCat.{1} ℤ) :
    Functor.whiskerRight (toSheafify J P) (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R) ≫
      toSheafify J (sheafify J P ⋙ SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R) ≫
      ((presheafToSheafCompComposeAndSheafifyIso J (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R)).hom.app P).hom =
        toSheafify J (P ⋙ SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R) := by
  let e := (presheafToSheafCompComposeAndSheafifyIso J (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R)).app P
  have hi : e.inv.hom = sheafifyMap J
      (Functor.whiskerRight (toSheafify J P) (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R)) := rfl
  have h := toSheafify_naturality J
    (Functor.whiskerRight (toSheafify J P) (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R))
  rw [← hi] at h
  rw [← Category.assoc, h, Category.assoc]
  change toSheafify J (P ⋙ SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R) ≫
    ((sheafToPresheaf _ _).map e.inv ≫ (sheafToPresheaf _ _).map e.hom) = _
  rw [← Functor.map_comp, e.inv_hom_id]
  change toSheafify J (P ⋙ SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R) ≫ 𝟙 _ = _
  exact Category.comp_id _

omit [CharZero R] in
theorem constant_generator :
    let P := (Functor.const Cᵒᵖ).obj (ModuleCat.of ℤ (ULift.{1} ℤ))
    Functor.whiskerRight (toSheafify J P) (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R) ≫
      toSheafify J (sheafify J P ⋙ SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R) ≫ (ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).hom.hom =
        (Functor.constComp Cᵒᵖ (ModuleCat.of ℤ (ULift.{1} ℤ)) (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R)).hom ≫
          (Functor.const Cᵒᵖ).map (ConstantCoefficientUnit.ConstantCoefficientExtension.unitIso R).hom ≫
            toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R)) := by
  let P := (Functor.const Cᵒᵖ).obj (ModuleCat.of ℤ (ULift.{1} ℤ))
  let c := (Functor.constComp Cᵒᵖ (ModuleCat.of ℤ (ULift.{1} ℤ)) (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R)).hom
  let d := (Functor.const Cᵒᵖ).map (ConstantCoefficientUnit.ConstantCoefficientExtension.unitIso R).hom
  change Functor.whiskerRight (toSheafify J P) (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R) ≫
    toSheafify J (sheafify J P ⋙ SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R) ≫
      (((presheafToSheafCompComposeAndSheafifyIso J (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R)).hom.app P).hom ≫
        sheafifyMap J c ≫ sheafifyMap J d) =
      c ≫ d ≫ toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R))
  rw [extension_generator_assoc, ← toSheafify_naturality_assoc, ← toSheafify_naturality]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafExtension.SheafExtensionGenerators
