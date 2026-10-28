import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorusIntegralInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSheafCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafCoefficientInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeQuotientLocalTopology
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HolomorphicPeriod

/-! # Integral Sheaf Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegralSheafCoefficients

noncomputable section

section

/-! The actual integral, rational, and rational-mod-integral locally
constant sequence detects the integral degree-two obstruction. -/

open _root_.CategoryTheory _root_.TopologicalSpace

instance rationalModuloIntegral_divisible : DivisibleBy TorusIntegralInjection.RationalModuloIntegral ℤ := by
  let : DivisibleBy ℚ ℕ := AddGroup.divisibleByNatOfDivisibleByInt ℚ
  let : DivisibleBy TorusIntegralInjection.RationalModuloIntegral ℕ := inferInstance
  exact AddGroup.divisibleByIntOfDivisibleByNat TorusIntegralInjection.RationalModuloIntegral

theorem integralRationalModulo_comp_zero (a : ℤ) :
    TorusIntegralInjection.rationalModuloCoefficient (TorusIntegralInjection.integralRationalCoefficient a) = 0 :=
  (TorusIntegralInjection.integralRationalModulo_exact _).mpr ⟨a, rfl⟩

def integerRationalSheafSequence (X : TopCat.{0}) :=
  LocallyConstantCoefficientExact.locallyConstantCoefficientSequence TorusIntegralInjection.integralRationalCoefficient TorusIntegralInjection.rationalModuloCoefficient X
    integralRationalModulo_comp_zero

theorem integerRationalSheafSequence_shortExact (X : TopCat.{0}) :
    (integerRationalSheafSequence X).ShortExact :=
  LocallyConstantCoefficientExact.locallyConstantCoefficientSequence_shortExact TorusIntegralInjection.integralRationalCoefficient TorusIntegralInjection.rationalModuloCoefficient X
    integralRationalModulo_comp_zero TorusIntegralInjection.integralRationalCoefficient_injective TorusIntegralInjection.rationalModuloCoefficient_surjective
    (fun b => (TorusIntegralInjection.integralRationalModulo_exact b).mp)

theorem integralSheafH2_injective_of_singularModuloLift (X : TopCat.{0})
    [MetrizableSpace X] [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]
    (h1 : Function.Surjective (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap TorusIntegralInjection.rationalModuloCoefficient X 1)) :
    Function.Injective ((Sheaf.functorH (Opens.grothendieckTopology X) 2).map
      (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap TorusIntegralInjection.integralRationalCoefficient X)) := by
  have := AlgebraicTopology.Cohomology.Singular.IntegralCoefficientInjective.injective_intModule_of_divisible (ModuleCat.of ℤ TorusIntegralInjection.RationalModuloIntegral)
  have h := IntegerSheafCoefficient.sheafH1_coefficient_surjective_of_singular TorusIntegralInjection.rationalModuloCoefficient X h1
  exact SheafCoefficientInjection.sheafH2_injective_of_H1_surjective (X := X) (S := integerRationalSheafSequence X)
    (integerRationalSheafSequence_shortExact X) h

theorem torus_integralSheafH2_rational_injective
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [SecondCountableTopology V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [Module.Free ℤ Λ] :
    Function.Injective ((Sheaf.functorH (Opens.grothendieckTopology (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) 2).map
      (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap TorusIntegralInjection.integralRationalCoefficient (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ))) := by
  let := LatticeQuotientLocalTopology.latticeQuotient_stronglyLocallyContractible Λ
  let := LatticeQuotientLocalTopology.latticeQuotient_locallyPathConnected Λ
  let := LatticeQuotientLocalTopology.latticeQuotient_metrizable Λ
  exact integralSheafH2_injective_of_singularModuloLift (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)
    (SingularCoefficientLift.singularH1_coefficient_surjective TorusIntegralInjection.rationalModuloCoefficient TorusIntegralInjection.rationalModuloCoefficient_surjective Λ)

end

/-! Identify the constructed coefficient sheaves and maps with the
original ChernClass integral and rational sheaves. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HolomorphicPeriod

variable (X : TopCat.{0})

def originalIntegralConstantIso :
    IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf (ModuleCat.of ℤ ℤ) X ≅ DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf X := by
  apply (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).preimageIso
  exact NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    apply LocallyConstant.ext
    intro x
    rfl)

def originalRationalConstantIso :
    IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf (ModuleCat.of ℤ ℚ) X ≅ DivisorClass.Chern.Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X := by
  apply (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).preimageIso
  exact NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    apply LocallyConstant.ext
    intro x
    rfl)

theorem originalIntegralRationalConstantMap :
    LocallyConstantCoefficientExact.integerLocallyConstantSheafMap TorusIntegralInjection.integralRationalCoefficient X ≫ (originalRationalConstantIso X).hom =
      (originalIntegralConstantIso X).hom ≫ DivisorClass.Chern.Rational.HolomorphicPeriod.integralToRationalConstantSheaf X := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply LocallyConstant.ext
  intro x
  rfl

theorem additiveMap_injective_of_comparison_isos
    {A B C D : AddCommGrpCat.{0}} (f : A ⟶ B) (g : C ⟶ D) (eA : A ≅ C) (eB : B ≅ D)
    (h : f ≫ eB.hom = eA.hom ≫ g) (hf : Function.Injective f) : Function.Injective g := by
  have he (x : C) : eB.hom (f (eA.inv x)) = g x := by
    have hx := ConcreteCategory.congr_hom h (eA.inv x)
    simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] using hx
  intro a b hab
  apply eA.addCommGroupIsoToAddEquiv.symm.injective
  apply hf
  apply eB.addCommGroupIsoToAddEquiv.injective
  exact (he a).trans (hab.trans (he b).symm)

theorem originalIntegralSheafH2_injective_of_singularModuloLift
    [MetrizableSpace X] [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]
    (h1 : Function.Surjective (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap TorusIntegralInjection.rationalModuloCoefficient X 1)) :
    Function.Injective ((Sheaf.functorH (Opens.grothendieckTopology X) 2).map
      (DivisorClass.Chern.Rational.HolomorphicPeriod.integralToRationalConstantSheaf X)) := by
  let H := Sheaf.functorH (Opens.grothendieckTopology X) 2
  have hp := congrArg H.map (originalIntegralRationalConstantMap X)
  have hp' : H.map (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap TorusIntegralInjection.integralRationalCoefficient X) ≫
      H.map (originalRationalConstantIso X).hom =
    H.map (originalIntegralConstantIso X).hom ≫ H.map (DivisorClass.Chern.Rational.HolomorphicPeriod.integralToRationalConstantSheaf X) :=
    (H.map_comp _ _).symm.trans (hp.trans (H.map_comp _ _))
  exact additiveMap_injective_of_comparison_isos _ _
    (H.mapIso (originalIntegralConstantIso X)) (H.mapIso (originalRationalConstantIso X)) hp'
    (integralSheafH2_injective_of_singularModuloLift X h1)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegralSheafCoefficients
