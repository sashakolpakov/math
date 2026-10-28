import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps

/-! # Period Projection Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality.IntrinsicLinearMaps

noncomputable section

/-! The genuine complexified period projection intertwines algebraic
group maps and their constructed native complex-linear lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}

theorem complexPeriodProjection_natural (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f).baseChange ℂ u) =
      Intrinsic.Maps.IntrinsicLinearMaps.linearLift f (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul z u =>
      rw [LinearMap.baseChange_tmul, Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_tmul,
        Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_tmul, map_smul]
      rfl

theorem rationalLift_isHodgeMap (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f) := by
  intro u hu
  change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f).baseChange ℂ u) = 0
  exact (complexPeriodProjection_natural f u).trans
    ((congrArg (Intrinsic.Maps.IntrinsicLinearMaps.linearLift f) hu).trans (Intrinsic.Maps.IntrinsicLinearMaps.linearLift f).map_zero)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality.IntrinsicLinearMaps
