import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntegerSheafEquivalence

/-! # Constant Coefficient Extension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ConstantCoefficientExtension.IntegralConstantCoefficientExtension

noncomputable section

/-! The actual integer generator becomes the actual rank-one flat-ring coefficient sheaf under the constructed coefficient adjunction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntegerSheafEquivalence.IntegralIntegerSheafEquivalence

variable (R : Type) [CommRing R] [Module.Flat ℤ R]

def unitIso : (SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.extendCoefficients R).obj (ModuleCat.of ℤ (ULift.{0} ℤ)) ≅ ModuleCat.of R R := by
  let M := (SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.restrictCoefficients R).obj (ModuleCat.of R R)
  let : Module R M := @Semiring.toModule R inferInstance
  let : Module ℤ M := M.isModule
  have : @IsScalarTower ℤ R M (Algebra.toSMul : SMul ℤ R)
      (inferInstance : SMul R M) M.isModule.toSMul := by
    exact @IsScalarTower.of_algebraMap_smul ℤ R M _ _ (inferInstance : Algebra ℤ R)
      (inferInstance : MulAction R M) M.isModule.toSMul (fun n w =>
        (ModuleCat.restrictScalars.smul_def (Int.castRingHom R)
          (M := ModuleCat.of R R) n (show R from w)).symm)
  exact ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R M)
    (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ)).trans
      (TensorProduct.AlgebraTensorModule.rid ℤ R M)).toModuleIso

variable {C : Type} [Category.{0} C] (J : GrothendieckTopology C)

def constantIso :
    (SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.extendSheaf R J).obj ((constantSheaf J (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))) ≅
    (constantSheaf J (ModuleCat.{0} R)).obj (ModuleCat.of R R) :=
  (presheafToSheafCompComposeAndSheafifyIso J (SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.extendCoefficients R)).app
      ((Functor.const Cᵒᵖ).obj (ModuleCat.of ℤ (ULift.{0} ℤ))) ≪≫
    (presheafToSheaf J (ModuleCat.{0} R)).mapIso
      (Functor.constComp Cᵒᵖ (ModuleCat.of ℤ (ULift.{0} ℤ)) (SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction.extendCoefficients R)) ≪≫
    (constantSheaf J (ModuleCat.{0} R)).mapIso (unitIso R)

def forgetConstantIso :
    (IntegerSheafEquivalence.IntegralIntegerSheafEquivalence.forgetSheaf J).obj ((constantSheaf J (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))) ≅
    (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  (constantCommuteCompose J (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0})).app
    (ModuleCat.of ℤ (ULift.{0} ℤ))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ConstantCoefficientExtension.IntegralConstantCoefficientExtension
