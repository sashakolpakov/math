import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPeriod
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Rational

/-! # Rational Period -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod

noncomputable section

/-! The rational span of the literal integral period lattice is its
scalar extension from Z to Q. The comparison preserves the actual vectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

local instance : IsIntegral A.toOver.left := A.variety.property

def integralPeriodInclusion : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A →ₗ[ℤ] AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A where
  toFun x := ⟨x.val, Submodule.subset_span x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rationalPeriodsFromIntegral : ℚ ⊗[ℤ] HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A →ₗ[ℚ] AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℚ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A →ₗ[ℤ] AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) (integralPeriodInclusion A))

@[simp] theorem rationalPeriodsFromIntegral_tmul (r : ℚ) (x : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    rationalPeriodsFromIntegral A (r ⊗ₜ[ℤ] x) = r • integralPeriodInclusion A x := rfl

theorem rationalPeriodsFromIntegral_basis
    (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) :
    rationalPeriodsFromIntegral A (1 ⊗ₜ[ℤ] AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A i) = AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i := by
  rw [rationalPeriodsFromIntegral_tmul, one_smul]
  apply Subtype.ext
  exact (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis_coe A i).symm

theorem rationalPeriodsFromIntegral_eq_basisEquiv :
    rationalPeriodsFromIntegral A =
      (((AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A).baseChange ℚ).equiv (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A) (Equiv.refl _)).toLinearMap := by
  apply ((AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A).baseChange ℚ).ext
  intro i
  rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply,
    Module.Basis.baseChange_apply, rationalPeriodsFromIntegral_basis]

def rationalPeriodsEquiv : ℚ ⊗[ℤ] HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A ≃ₗ[ℚ] AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A :=
  LinearEquiv.ofBijective (rationalPeriodsFromIntegral A) (by
    rw [rationalPeriodsFromIntegral_eq_basisEquiv]
    exact (((AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A).baseChange ℚ).equiv
      (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A) (Equiv.refl _)).bijective)

@[simp] theorem rationalPeriodsEquiv_tmul (r : ℚ) (x : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    rationalPeriodsEquiv A (r ⊗ₜ[ℤ] x) = r • integralPeriodInclusion A x := rfl

variable (q : ℕ) [Fact q.Prime]

/-- Both paths extend the same literal integral periods to Q_q. -/
def rationalPeriodTateEquiv :
    ℚ_[q] ⊗[ℚ] AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ_[q]]
      Rational.rationalTateModule A.toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q :=
  (LinearEquiv.baseChange ℚ ℚ_[q] _ _ (rationalPeriodsEquiv A)).symm.trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℚ_[q] ℚ_[q] (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℤ_[q] ℚ_[q] ℚ_[q] (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).symm.trans
        (LinearEquiv.baseChange ℤ_[q] ℚ_[q] _ _ (IntrinsicPeriod.nativeCompletedPeriodTateEquiv q A))))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod
