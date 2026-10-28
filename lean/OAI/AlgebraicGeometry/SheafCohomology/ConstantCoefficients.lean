import OAI.AlgebraicGeometry.SheafCohomology.IntegerCoefficients
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Constant Coefficients -/

namespace OAI.AlgebraicGeometry.SheafCohomology.ConstantCoefficients.Projective

noncomputable section

/-! Identification of the constant sheaves used in coefficient comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
def complexExtensionUnitIso :
    CoefficientFlatness.Projective.extendComplexCoefficients.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℂ ℂ := by
  let M := (ModuleCat.restrictScalars (Int.castRingHom ℂ)).obj (ModuleCat.of ℂ ℂ)
  letI : Module ℂ M := inferInstanceAs (Module ℂ ℂ)
  letI : Module ℤ M := M.isModule
  have : @IsScalarTower ℤ ℂ M (Algebra.toSMul : SMul ℤ ℂ)
      (inferInstance : SMul ℂ M) M.isModule.toSMul := by
    refine @IsScalarTower.mk ℤ ℂ M (Algebra.toSMul : SMul ℤ ℂ)
      (inferInstance : SMul ℂ M) M.isModule.toSMul ?_
    intro n z w
    dsimp [M, ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj', Module.compHom]
    simp only [zsmul_eq_mul, mul_assoc]
    exact (ModuleCat.restrictScalars.smul_def (Int.castRingHom ℂ)
      (M := ModuleCat.of ℂ ℂ) n (z * (show ℂ from w))).symm
  exact (TensorProduct.AlgebraTensorModule.rid ℤ ℂ M).toModuleIso

def extendConstantComplexIso (X : TopCat.{0}) :
    (Coefficients.Projective.extendComplexSheaf X).obj
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)).obj
          (ModuleCat.of ℤ ℤ)) ≅
      (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
        (ModuleCat.of ℂ ℂ) :=
  (presheafToSheafCompComposeAndSheafifyIso (Opens.grothendieckTopology X)
      CoefficientFlatness.Projective.extendComplexCoefficients).app ((Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of ℤ ℤ)) ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).mapIso
      (Functor.constComp (Opens X)ᵒᵖ (ModuleCat.of ℤ ℤ) CoefficientFlatness.Projective.extendComplexCoefficients) ≪≫
    (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).mapIso
      complexExtensionUnitIso

def forgetConstantIntegerIso (X : TopCat.{0}) :
    (IntegerCoefficients.Projective.integerSheafForget X).obj
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)).obj
          (ModuleCat.of ℤ ℤ)) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of ℤ) :=
  (constantCommuteCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0})).app (ModuleCat.of ℤ ℤ)

def constantIntegerUliftIso (X : TopCat.{0}) :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of ℤ) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapIso
    (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).symm.toAddCommGrpIso

end

end OAI.AlgebraicGeometry.SheafCohomology.ConstantCoefficients.Projective
