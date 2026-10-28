import OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.CycleStratumRealization

/-! # Cycle Isomorphism Dimensions -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CycleIsomorphismDimensions

noncomputable section

/-!
# Analytic model dimensions under actual algebraic isomorphisms

These equalities follow from the actual function fields and the proved
dimensions of the native analytic models. The resulting complex linear
equivalences may be used to compare normal coordinates without introducing
any assumption about cohomology or Thom classes.
-/

open _root_.CategoryTheory

namespace IntegralProjectiveVariety

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

/-- The actual complex dimensions are invariant under an isomorphism over the base. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_of_overIso (e : V.toOver ≅ W.toOver) :
    V.complexDimension = W.complexDimension :=
  (AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension V.structureMap).symm.trans
    ((AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.varietyIso_transcendenceDimension e).trans
      (AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension W.structureMap))

/-- The native ambient chart models have the same complex dimension. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticModel_finrank_eq_of_overIso (e : V.toOver ≅ W.toOver) :
    Module.finrank ℂ V.analyticModel = Module.finrank ℂ W.analyticModel := by
  rw [V.analyticModel_complex_finrank, W.analyticModel_complex_finrank]
  exact AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_of_overIso e

/-- A genuine complex linear coordinate equivalence between the native ambient models. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticModelEquivOfIso (e : V.toOver ≅ W.toOver) :
    V.analyticModel ≃L[ℂ] W.analyticModel :=
  ContinuousLinearEquiv.ofFinrankEq (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticModel_finrank_eq_of_overIso e)

end IntegralProjectiveVariety

namespace DimensionCycleSupport

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- Transporting a support preserves the dimension of its actual regular locus. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension =
      Z.regularComplexDimension := by
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_eq_supportDimension,
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_eq_supportDimension, AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv_val]
  exact AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.varietyIso_supportTranscendenceDimension e Z.val

/-- The native regular-locus chart models have equal complex dimension. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticModel_finrank_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Module.finrank ℂ Z.regularAnalyticModel =
      Module.finrank ℂ (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAnalyticModel := by
  rw [Z.regularAnalyticModel_complex_finrank,
    (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAnalyticModel_complex_finrank,
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_of_overIso e]

/-- A complex linear coordinate equivalence for the two actual regular-locus models. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticModelEquivOfIso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularAnalyticModel ≃L[ℂ] (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAnalyticModel :=
  ContinuousLinearEquiv.ofFinrankEq (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticModel_finrank_iso e Z)

end DimensionCycleSupport

end

end OAI.AlgebraicTopology.DeRham.Comparison.CycleIsomorphismDimensions
