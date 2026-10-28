import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection
import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods

/-! # Marked Rational Periods -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedRationalPeriods

noncomputable section

/-! Any full integral marking of the actual exponential lattice gives
rational coordinates and the same actual complex period matrix. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods

variable {I : Type} [Fintype I] (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking I A)

local instance : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property
local instance : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A

omit [Fintype I] in
theorem rationalPeriods_eq_span_marking : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A =
    Submodule.span ℚ (Set.range (b.ofZLatticeBasis ℝ)) := by
  change Submodule.span ℚ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A : Set (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) = _
  conv_lhs => rw [← b.ofZLatticeBasis_span ℝ]
  exact Submodule.span_span_of_tower ℤ ℚ _

def markedRationalPeriodBasis : Module.Basis I ℚ (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :=
  (Module.Basis.span ((b.ofZLatticeBasis ℝ).linearIndependent.restrict_scalars' ℚ)).map
    (LinearEquiv.ofEq _ _ (rationalPeriods_eq_span_marking A b).symm)

omit [Fintype I] in
theorem markedRationalPeriodBasis_coe (i : I) :
    (markedRationalPeriodBasis A b i).val = (b i).val := by
  change (Module.Basis.span ((b.ofZLatticeBasis ℝ).linearIndependent.restrict_scalars' ℚ) i).val = _
  exact (Module.Basis.coe_span_apply _ i).trans
    (Module.Basis.ofZLatticeBasis_apply ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) b i)

def markedRationalPeriodCoordinates : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] (I → ℚ) :=
  (markedRationalPeriodBasis A b).equivFun

def markedComplexPeriodCoordinates : ComplexMultiplication.WeightOne.CM.Complexification (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) ≃ₗ[ℂ] (I → ℂ) :=
  ((markedRationalPeriodBasis A b).baseChange ℂ).equivFun

theorem markedComplexPeriodCoordinates_projection (v : I → ℂ) :
    AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A ((markedComplexPeriodCoordinates A b).symm v) =
      ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b v := by
  let B := (markedRationalPeriodBasis A b).baseChange ℂ
  have h (i : I) : AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (B i) = (b i).val := by
    rw [Module.Basis.baseChange_apply, AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_tmul, one_smul,
      markedRationalPeriodBasis_coe]
  rw [show (markedComplexPeriodCoordinates A b).symm v = ∑ i, v i • B i from
    B.equivFun_symm_apply v]
  simp only [map_sum, map_smul, h, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_apply]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedRationalPeriods
