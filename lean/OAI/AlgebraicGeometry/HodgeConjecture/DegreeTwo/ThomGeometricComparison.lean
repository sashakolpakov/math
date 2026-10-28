import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomTrace
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass

/-! # Thom Geometric Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomGeometricComparison.Constructions

noncomputable section

/-! The normalized divisor Thom class and the independently constructed geometric fundamental-trace class differ by the proved nonzero local product coefficient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularAbsoluteThomClass_eq_geometric :
    Z.regularAbsoluteThomClass =
      LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension • Z.regularGeometricCycleClass := by
  apply (AlgebraicTopology.Duality.Poincare.CompactSupportAnd.cohomology_eq_iff_compactSupportEvaluation_eq V.complexDimension
    2 (2*Z.regularComplexDimension) Z.regularGeometricTrace_degree _ _).mpr
  intro b
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, Z.regularGeometricCycleClass_evaluation]
  exact CompactThomTrace.Constructions.regularThomClass_geometric_evaluation Z b

theorem rationalCycleClass_eq_geometric :
    Z.rationalCycleClass =
      LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension • Z.geometricCycleClass := by
  apply Z.regularAmbientCohomologyRestriction_injective
  rw [Z.regularAmbientCohomologyRestriction_cycleClass, map_smul, Z.geometricCycleClass_regularRestriction]
  exact regularAbsoluteThomClass_eq_geometric Z

theorem geometricCycleClass_eq_thom :
    Z.geometricCycleClass =
      (LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension)⁻¹ • Z.rationalCycleClass := by
  rw [rationalCycleClass_eq_geometric Z, inv_smul_smul₀
    (LocalProductCoefficient.Constructions.localProductCupCoefficient_ne_zero 1 Z.regularComplexDimension)]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomGeometricComparison.Constructions
