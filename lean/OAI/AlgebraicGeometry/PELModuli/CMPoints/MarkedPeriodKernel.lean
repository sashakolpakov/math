import OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedRationalPeriods

/-! # Marked Period Kernel -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedPeriodKernel

noncomputable section

/-! The marked matrix kernel is exactly the native period kernel in
the constructed integral coordinates, with its intrinsic dimension. -/

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property

theorem markedPeriodKernel_eq_map {I : Type} [Fintype I]
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking I A) :
    (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker =
      (AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker.map (MarkedRationalPeriods.markedComplexPeriodCoordinates A b).toLinearMap := by
  ext v
  rw [Submodule.mem_map_equiv]
  change ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b v = 0 ↔
    AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A ((MarkedRationalPeriods.markedComplexPeriodCoordinates A b).symm v) = 0
  rw [MarkedRationalPeriods.markedComplexPeriodCoordinates_projection]

theorem markedPeriodKernel_finrank {I : Type} [Fintype I]
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking I A) :
    Module.finrank ℂ (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom := by
  rw [markedPeriodKernel_eq_map, (MarkedRationalPeriods.markedComplexPeriodCoordinates A b).finrank_map_eq,
    AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_ker_finrank]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedPeriodKernel
