import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegerSheaf

/-! # Constant Coefficient Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientUnit.ConstantCoefficientExtension

noncomputable section

/-! The actual integer generator becomes the actual rank-one field coefficient sheaf under the constructed coefficient adjunction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientCo.SheafCoefficientAdjunction OAI.NumberTheory.PadicHodge.GeometricComparison.IntegerSheaf.IntegerSheafEquivalence

variable (R : Type 1) [Field R] [CharZero R]

def unitIso : (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R).obj (ModuleCat.of ℤ (ULift.{1} ℤ)) ≅ ModuleCat.of R R := by
  let M := (SheafCoefficientCo.SheafCoefficientAdjunction.restrictCoefficients R).obj (ModuleCat.of R R)
  letI : Module R M := @Semiring.toModule R inferInstance
  letI : Module ℤ M := M.isModule
  have : @IsScalarTower ℤ R M (Algebra.toSMul : SMul ℤ R)
      (inferInstance : SMul R M) M.isModule.toSMul := by
    exact @IsScalarTower.of_algebraMap_smul ℤ R M _ _ (inferInstance : Algebra ℤ R)
      (inferInstance : MulAction R M) M.isModule.toSMul (fun n w =>
        (ModuleCat.restrictScalars.smul_def (Int.castRingHom R)
          (M := ModuleCat.of R R) n (show R from w)).symm)
  exact ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R M)
    (ULift.moduleEquiv : ULift.{1} ℤ ≃ₗ[ℤ] ℤ)).trans
      (TensorProduct.AlgebraTensorModule.rid ℤ R M)).toModuleIso

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C)

def constantIso :
    (SheafCoefficientCo.SheafCoefficientAdjunction.extendSheaf R J).obj ((constantSheaf J (ModuleCat.{1} ℤ)).obj
      (ModuleCat.of ℤ (ULift.{1} ℤ))) ≅
    (constantSheaf J (ModuleCat.{1} R)).obj (ModuleCat.of R R) :=
  (presheafToSheafCompComposeAndSheafifyIso J (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R)).app
      ((Functor.const Cᵒᵖ).obj (ModuleCat.of ℤ (ULift.{1} ℤ))) ≪≫
    (presheafToSheaf J (ModuleCat.{1} R)).mapIso
      (Functor.constComp Cᵒᵖ (ModuleCat.of ℤ (ULift.{1} ℤ)) (SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R)) ≪≫
    (constantSheaf J (ModuleCat.{1} R)).mapIso (unitIso R)

def forgetConstantIso :
    (IntegerSheaf.IntegerSheafEquivalence.forgetSheaf J).obj ((constantSheaf J (ModuleCat.{1} ℤ)).obj
      (ModuleCat.of ℤ (ULift.{1} ℤ))) ≅
    (constantSheaf J AddCommGrpCat.{1}).obj (AddCommGrpCat.of (ULift.{1} ℤ)) :=
  (constantCommuteCompose J (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1})).app
    (ModuleCat.of ℤ (ULift.{1} ℤ))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientUnit.ConstantCoefficientExtension
