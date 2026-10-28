import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps

/-! # Rational Period Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriodNaturality

noncomputable section

/-! Rational period–Tate comparison commutes with actual algebraic group
maps, so it also transports the genuine integral PEL action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

theorem rationalPeriodsEquiv_symm_integral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (x : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    (RationalPeriod.rationalPeriodsEquiv A).symm (RationalPeriod.integralPeriodInclusion A x) = 1 ⊗ₜ[ℤ] x := by
  apply (RationalPeriod.rationalPeriodsEquiv A).injective
  rw [LinearEquiv.apply_symm_apply, RationalPeriod.rationalPeriodsEquiv_tmul, one_smul]

theorem rationalLift_integral (f : A.toOver ⟶ B.toOver) [IsMonHom f] (x : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f (RationalPeriod.integralPeriodInclusion A x) = RationalPeriod.integralPeriodInclusion B (IntrinsicPeriod.nativePeriodLatticeMap f x) := rfl

theorem rationalPeriodsEquiv_natural (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f).comp (RationalPeriod.rationalPeriodsEquiv A).toLinearMap =
      (RationalPeriod.rationalPeriodsEquiv B).toLinearMap.comp ((IntrinsicPeriod.nativePeriodLatticeMap f).baseChange ℚ) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, RationalPeriod.rationalPeriodsEquiv_tmul,
      LinearMap.baseChange_tmul, map_smul, rationalLift_integral]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (q : ℕ) [Fact q.Prime]

theorem rationalPeriodTateEquiv_tmul_integral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (z : ℚ_[q]) (x : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    RationalPeriod.rationalPeriodTateEquiv A q (z ⊗ₜ[ℚ] RationalPeriod.integralPeriodInclusion A x) =
      z ⊗ₜ[ℤ_[q]] IntrinsicPeriod.nativeCompletedPeriodTateEquiv q A (1 ⊗ₜ[ℤ] x) := by
  simp only [RationalPeriod.rationalPeriodTateEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_symm_tmul, rationalPeriodsEquiv_symm_integral,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul]

theorem rationalPeriodTateEquiv_basis (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) :
    RationalPeriod.rationalPeriodTateEquiv A q (1 ⊗ₜ[ℚ] AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i) =
      (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] IntrinsicPeriod.nativeCompletedPeriodTateEquiv q A (1 ⊗ₜ[ℤ] AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A i) := by
  have h : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i = RationalPeriod.integralPeriodInclusion A (AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A i) :=
    Subtype.ext (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis_coe A i)
  rw [h, rationalPeriodTateEquiv_tmul_integral]

theorem rationalPeriodTate_natural (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    (Rational.rationalTateMap (A := A.toOver) (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f).comp
        (RationalPeriod.rationalPeriodTateEquiv A q).toLinearMap =
      (RationalPeriod.rationalPeriodTateEquiv B q).toLinearMap.comp ((AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f).baseChange ℚ_[q]) := by
  apply ((AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A).baseChange ℚ_[q]).ext
  intro i
  simp only [LinearMap.comp_apply, Module.Basis.baseChange_apply, LinearEquiv.coe_coe,
    rationalPeriodTateEquiv_basis, Rational.rationalTateMap, LinearMap.baseChange_tmul]
  have h : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i = RationalPeriod.integralPeriodInclusion A (AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A i) :=
    Subtype.ext (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis_coe A i)
  rw [h, rationalLift_integral, rationalPeriodTateEquiv_tmul_integral]
  have hn := LinearMap.congr_fun (IntrinsicPeriod.nativeCompletedPeriodTate_natural q f)
    (1 ⊗ₜ[ℤ] AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A i)
  change Add.schemeTateMap A.toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q f
    (IntrinsicPeriod.nativeCompletedPeriodTateEquiv q A (1 ⊗ₜ[ℤ] AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A i)) =
      IntrinsicPeriod.nativeCompletedPeriodTateEquiv q B
        (1 ⊗ₜ[ℤ] IntrinsicPeriod.nativePeriodLatticeMap f (AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A i)) at hn
  exact congrArg (fun z => (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] z) hn

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriodNaturality
