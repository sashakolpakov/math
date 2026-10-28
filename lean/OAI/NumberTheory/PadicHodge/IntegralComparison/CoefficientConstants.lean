import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatCoefficientSheaves

/-! # Coefficient Constants -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientConstants

noncomputable section

/-!
# IntegralComparison: constant unit sheaves under coefficient extension

The tensor-unit isomorphism identifies extension of the constant source
ring sheaf with the constant target ring sheaf. This identifies the
specific sources used for cohomology in the coefficient Ext adjunction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

def extensionUnitIso :
    (FlatCoefficientSheaves.extendCoefficients S R).obj (ModuleCat.of S S) ≅ ModuleCat.of R R := by
  let M := (ModuleCat.restrictScalars (algebraMap S R)).obj (ModuleCat.of R R)
  letI : Module R M := inferInstanceAs (Module R R)
  letI : Module S M := M.isModule
  have : @IsScalarTower S R M (Algebra.toSMul : SMul S R)
      (inferInstance : SMul R M) M.isModule.toSMul := by
    refine @IsScalarTower.mk S R M (Algebra.toSMul : SMul S R)
      (inferInstance : SMul R M) M.isModule.toSMul ?_
    intro s r m
    rw [Algebra.smul_def]
    change ((algebraMap S R) s * r) * (show R from m) =
      (algebraMap S R) s * (r * (show R from m))
    exact mul_assoc _ _ _
  exact (TensorProduct.AlgebraTensorModule.rid S R M).toModuleIso

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [HasSheafify J (ModuleCat.{u} S)] [HasSheafify J (ModuleCat.{u} R)]

def extensionConstantIso :
    (FlatCoefficientSheaves.extension S R J).obj
        ((constantSheaf J (ModuleCat.{u} S)).obj (ModuleCat.of S S)) ≅
      (constantSheaf J (ModuleCat.{u} R)).obj (ModuleCat.of R R) :=
  (presheafToSheafCompComposeAndSheafifyIso J
      (FlatCoefficientSheaves.extendCoefficients S R)).app ((Functor.const Cᵒᵖ).obj (ModuleCat.of S S)) ≪≫
    (presheafToSheaf J (ModuleCat.{u} R)).mapIso
      (Functor.constComp Cᵒᵖ (ModuleCat.of S S) (FlatCoefficientSheaves.extendCoefficients S R)) ≪≫
    (constantSheaf J (ModuleCat.{u} R)).mapIso (extensionUnitIso S R)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientConstants
