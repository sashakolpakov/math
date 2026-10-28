import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodPolarization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.Canonical

/-! # Intrinsic Period Pairing -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicPeriodPairing

noncomputable section

/-! The actual polarization identifies rational native periods with
the actual singular H1. Its complexification has the prescribed integral
period values, with the original singular-cohomology normalization. -/

open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A))

def nativePeriodH1Equiv : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] A.variety.rationalCohomology 1 :=
  (P.form.toDual P.nondegenerate).trans (AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A).symm

theorem nativePeriodH1Equiv_pair (u v : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A (nativePeriodH1Equiv A P u) v = P.form u v := by
  change AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A ((AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A).symm (P.form.toDual P.nondegenerate u)) v = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem nativePeriodH1Equiv_complex_period
    (u : ComplexMultiplication.WeightOne.CM.Complexification (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1
        ((nativePeriodH1Equiv A P).toLinearMap.baseChange ℂ u)) ℓ =
      P.form.baseChange ℂ u
        ((1 : ℂ) ⊗ₜ[ℚ] AbelianModuli.ReferenceFamily.LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) := by
  let w : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A := AbelianModuli.ReferenceFamily.LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ
  change HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1
      ((nativePeriodH1Equiv A P).toLinearMap.baseChange ℂ u)) ℓ =
    P.form.baseChange ℂ u ((1 : ℂ) ⊗ₜ[ℚ] w)
  induction u using TensorProduct.inductionOn with
  | tmul z u =>
    rw [LinearMap.baseChange_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
    let v : A.variety.complexCohomology 1 :=
      AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 1 (nativePeriodH1Equiv A P u)
    change HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A
      (z • v) ℓ = _
    rw [map_smul]
    change z * AbelianModuli.ReferenceFamily.Intrinsic.ComplexPeriods.IntrinsicComplexPeriods.complexPeriods A
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 1 (nativePeriodH1Equiv A P u)) ℓ = _
    have h := AbelianModuli.ReferenceFamily.Intrinsic.ComplexPeriods.IntrinsicComplexPeriods.complexPeriods_rationalToComplex A
      (nativePeriodH1Equiv A P u) ℓ
    have hp := congrArg (fun t : ℚ => (t : ℂ))
      (nativePeriodH1Equiv_pair A P u w)
    calc
      _ = z * (P.form u w : ℂ) :=
        congrArg (fun t : ℂ => z * t) (h.trans hp)
      _ = _ := by
        rw [LinearMap.BilinForm.baseChange_tmul, mul_one]
        simp only [Rat.smul_def, mul_comm]
  | add u v hu hv => simp only [map_add, AddMonoidHom.add_apply, LinearMap.add_apply, hu, hv]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicPeriodPairing
