import OAI.AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient

/-! # Rational Dual Complex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalDualComplex.Constructions

noncomputable section

/-! Rational-valued integral chain duality, retaining rational scalar structure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient

set_option backward.isDefEq.respectTransparency false

abbrev integralRationalDualComplex (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    CochainComplex (ModuleCat.{0} ℚ) ℕ where
  X n := ModuleCat.of ℚ (C.X n →ₗ[ℤ] ℚ)
  d i j := ModuleCat.ofHom {
    toFun := fun c => c.comp (C.d j i).hom
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  shape i j hij := by
    ext c z
    change c (C.d j i z) = 0
    rw [C.shape j i hij]
    exact map_zero c
  d_comp_d' i j k _ _ := by
    ext c z
    change c (C.d j i (C.d k j z)) = 0
    rw [← ConcreteCategory.comp_apply, C.d_comp_d]
    exact map_zero c

abbrev integralRationalDualEquiv (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (integralRationalDualComplex C).X n ≃ₗ[ℚ] (C.X n →ₗ[ℤ] ℚ) :=
  LinearEquiv.refl ℚ _

theorem integralRationalDualEquiv_d (C : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (i j : ℕ) (c : (integralRationalDualComplex C).X i) :
    integralRationalDualEquiv C j ((integralRationalDualComplex C).d i j c) =
      (integralRationalDualEquiv C i c).comp (C.d j i).hom := rfl

def integralRationalDualUniversalCoefficientEquiv
    (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (integralRationalDualComplex C).homology n ≃ₗ[ℚ] (C.homology n →ₗ[ℤ] ℚ) := by
  letI : CategoryTheory.Injective (ModuleCat.of ℤ ℚ) := AlgebraicTopology.Cohomology.Singular.IntegralCoefficientInjective.injective_restrictScalars_rat
  letI : Module.Injective ℤ ℚ := Module.injective_module_of_injective_object ℤ ℚ
  exact AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.InjectiveDuality.universalCoefficientEquiv C (integralRationalDualComplex C)
    (integralRationalDualEquiv C) (integralRationalDualEquiv_d C) n

theorem integralRationalDualUniversalCoefficientEquiv_class_class
    (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (integralRationalDualComplex C) n) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    integralRationalDualUniversalCoefficientEquiv C n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n c) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z) = c.val z.val :=
  AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.InjectiveDuality.homologyEvaluation_class_class C (integralRationalDualComplex C)
    (integralRationalDualEquiv C) (integralRationalDualEquiv_d C) n c z

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalDualComplex.Constructions
