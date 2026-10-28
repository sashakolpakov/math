import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientImage
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSheafCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegralSheafCoefficients

/-! # Sheaf Singular Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.SheafSingularImage

noncomputable section

/-! An integral sheaf lift forces an integral singular lift. Only the
quotient coefficient module needs an injective singular-to-sheaf comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {M N P : ModuleCat.{0} ℤ}
  (f : M ⟶ N) (g : N ⟶ P) (X : TopCat.{0})
  [MetrizableSpace X] [StronglyLocallyContractibleSpace X]
  [LocallyPathConnectedSpace X] [Injective P]

theorem singularCoefficient_lift_of_sheaf_lift
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : ∀ b : N, g b = 0 ↔ ∃ a : M, f a = b)
    (n : ℕ) (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology N X (n + 1))
    (b : (Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj
      (IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf M X))
    (hb : IntegerSingularSheafComparison.integerSingularBettiSheafMap N X n a =
      (Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map
        (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap f X) b) :
    ∃ c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M X (n + 1),
      AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X (n + 1) c = a := by
  apply SingularCoefficientImage.singularCoefficient_lift_of_zero f g X hf hg he n a
  apply (IntegerSingularSheafComparison.integerSingularBettiSheafIso P X n).addCommGroupIsoToAddEquiv.injective
  change IntegerSingularSheafComparison.integerSingularBettiSheafMap P X n (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X (n + 1) a) =
    IntegerSingularSheafComparison.integerSingularBettiSheafMap P X n 0
  have hn := ConcreteCategory.congr_hom (IntegerSheafCoefficient.integerSingularBettiSheafMap_naturality g X n) a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
  let H := Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)
  have hforget : (IntegerSingularSheafComparison.integerModuleForget.map (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X (n + 1))) a =
      AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X (n + 1) a := rfl
  have hgf := LocallyConstantCoefficientExact.integerLocallyConstantSheafMap_comp_zero f g X
    (fun x => (he (f x)).mpr ⟨x, rfl⟩)
  have hz : H.map (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap f X) ≫
      H.map (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap g X) = 0 :=
    (H.map_comp _ _).symm.trans ((congrArg H.map hgf).trans (H.map_zero _ _))
  calc
    IntegerSingularSheafComparison.integerSingularBettiSheafMap P X n (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X (n + 1) a) =
        IntegerSingularSheafComparison.integerSingularBettiSheafMap P X n
          ((IntegerSingularSheafComparison.integerModuleForget.map (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X (n + 1))) a) :=
      congrArg (fun x => IntegerSingularSheafComparison.integerSingularBettiSheafMap P X n x) hforget.symm
    _ = H.map (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap g X)
        (IntegerSingularSheafComparison.integerSingularBettiSheafMap N X n a) := hn
    _ = H.map (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap g X)
        (H.map (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap f X) b) :=
      congrArg (fun x => H.map (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap g X) x) hb
    _ = 0 := ConcreteCategory.congr_hom hz b
    _ = IntegerSingularSheafComparison.integerSingularBettiSheafMap P X n 0 :=
      (map_zero (IntegerSingularSheafComparison.integerSingularBettiSheafMap P X n).hom).symm

theorem singularIntegral_lift_of_sheafIntegral
    (n : ℕ) (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℤ ℚ) X (n + 1))
    (b : (Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj
      (IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf (ModuleCat.of ℤ ℤ) X))
    (hb : IntegerSingularSheafComparison.integerSingularBettiSheafMap (ModuleCat.of ℤ ℚ) X n a =
      (Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map
        (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap TorusIntegralInjection.integralRationalCoefficient X) b) :
    ∃ c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℤ ℤ) X (n + 1),
      AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap TorusIntegralInjection.integralRationalCoefficient X (n + 1) c = a := by
  have := AlgebraicTopology.Cohomology.Singular.IntegralCoefficientInjective.injective_intModule_of_divisible (ModuleCat.of ℤ TorusIntegralInjection.RationalModuloIntegral)
  exact singularCoefficient_lift_of_sheaf_lift TorusIntegralInjection.integralRationalCoefficient TorusIntegralInjection.rationalModuloCoefficient X
    TorusIntegralInjection.integralRationalCoefficient_injective TorusIntegralInjection.rationalModuloCoefficient_surjective
    TorusIntegralInjection.integralRationalModulo_exact n a b hb

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.SheafSingularImage
