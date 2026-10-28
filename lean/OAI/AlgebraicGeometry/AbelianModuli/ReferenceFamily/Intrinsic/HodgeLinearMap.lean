import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodComplementProjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality

/-! # Hodge Linear Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeLinearMap.IntrinsicRationalPeriods

noncomputable section

/-! An actual rational Hodge map induces a complex linear map on the
native tangent spaces through the genuine period projections. Its
values on rational periods are exactly the original rational map. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

def nativePeriodSection (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :=
  (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel A).subtype.comp (PeriodComplementProjection.IntrinsicRationalPeriods.conjugatePeriodProjectionEquiv A).symm.toLinearMap

theorem nativePeriodSection_projection (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (nativePeriodSection A v) = v :=
  (PeriodComplementProjection.IntrinsicRationalPeriods.conjugatePeriodProjectionEquiv A).apply_symm_apply v

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)

def nativeHodgeLinearMap : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B :=
  (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B).comp ((f.baseChange ℂ).comp (nativePeriodSection A))

theorem nativeHodgeLinearMap_projection
    (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B) f)
    (u : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    nativeHodgeLinearMap f (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u) = PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B (f.baseChange ℂ u) := by
  have hk : PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (u - nativePeriodSection A (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u)) = 0 := by
    rw [map_sub, nativePeriodSection_projection, sub_self]
  have hh := hf (u - nativePeriodSection A (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u)) hk
  change PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B (f.baseChange ℂ (u - nativePeriodSection A (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u))) = 0 at hh
  rw [map_sub, map_sub, sub_eq_zero] at hh
  exact hh.symm

theorem nativeHodgeLinearMap_rational
    (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B) f)
    (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) : nativeHodgeLinearMap f v.val = (f v).val := by
  have h := nativeHodgeLinearMap_projection f hf (1 ⊗ₜ[ℚ] v)
  rw [PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_tmul, one_smul, LinearMap.baseChange_tmul,
    PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_tmul, one_smul] at h
  exact h

theorem nativeHodgeLinearMap_preserves
    (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B) f)
    (hΛ : ∀ v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods A, f v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods B)
    (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (hv : v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) : nativeHodgeLinearMap f v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B := by
  let q : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A := ⟨v, Submodule.subset_span hv⟩
  have hq : q ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods A := hv
  have hr := hΛ q hq
  exact (congrArg (fun w : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B => w ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) (nativeHodgeLinearMap_rational f hf q)).mpr hr

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeLinearMap.IntrinsicRationalPeriods
