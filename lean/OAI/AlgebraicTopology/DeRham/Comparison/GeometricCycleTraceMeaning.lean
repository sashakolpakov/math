import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTrace
import OAI.AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality
import OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison

/-! # Geometric Cycle Trace Meaning -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTraceMeaning

noncomputable section

/-!
# The actual fundamental-class meaning of the geometric cycle trace

The independently defined geometric trace evaluates each compact-support
class on the actual proper relative pushforward of the integral compact
fundamental class. The same value is obtained from the genuine rational
locally finite fundamental class and its compact restriction after proper
pushforward. No supported cohomology class is used in these identifications.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison
open scoped TensorProduct ChangeOfRings _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace DimensionCycleSupport

variable {V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- At every compact support, the independent geometric trace is the
original class evaluated on the actual relative pushforward of the
integral compact fundamental class of the inverse compact subset. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_stage_pushforward (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (K : Compacts Z.regularAmbientSpace)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      (2 * Z.regularComplexDimension)) :
    Z.regularGeometricTrace
        (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
      Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of Z.regularAmbientSpace)
        (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) b
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap Z.regularComplementTopCatMap
          (A := (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))ᶜ)
          (B := (K : Set Z.regularAmbientSpace)ᶜ) (fun _ hx => hx)
          (2 * Z.regularComplexDimension)
          (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass Z.regularComplexDimension
            (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))
            (Z.isCompact_regularCompactPreimage (K : Set Z.regularAmbientSpace)
              K.isCompact))) := by
  rw [Z.regularGeometricTrace_stage]
  exact Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality
    Z.regularComplementTopCatMap (fun _ hx => hx)
    (2 * Z.regularComplexDimension) b _

/-- Rational evaluation on the genuine locally finite compact trace gives
the same geometric value. The unit coefficient is the one in the checked
rationalization of the integral compact fundamental class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_stage_nativeCompactTrace (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (K : Compacts Z.regularAmbientSpace)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      (2 * Z.regularComplexDimension)) :
    Z.regularGeometricTrace
        (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
      AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of Z.regularAmbientSpace)
        (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) b
        (AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
          Z.isProperMap_regularComplementTopCatMap (K : Set Z.regularAmbientSpace)
          K.isCompact (2 * Z.regularComplexDimension)
          Z.regularRationalLocallyFiniteFundamentalClass) := by
  rw [Z.regularGeometricTrace_stage,
    Duality.Poincare.RelativeRationalEvaluationComparison.relativeRationalHomologyEvaluation_eq_scalarEvaluation,
    Z.regularNativeFundamentalCompactTrace_eq_compactFundamental]
  exact AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality (ModuleCat.of ℚ ℚ)
    Z.regularComplementTopCatMap (fun _ hx => hx)
    (2 * Z.regularComplexDimension) b _

/-- Equivalently, push forward the actual rational locally finite
fundamental class first, then restrict to the retained compact set and
evaluate the original compact-support class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_stage_locallyFinitePushforward
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (K : Compacts Z.regularAmbientSpace)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      (2 * Z.regularComplexDimension)) :
    Z.regularGeometricTrace
        (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
      AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of Z.regularAmbientSpace)
        (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) b
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ (TopCat.of Z.regularAmbientSpace)
          (K : Set Z.regularAmbientSpace) K.isCompact (2 * Z.regularComplexDimension)
          (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℚ Z.regularComplementTopCatMap
            Z.isProperMap_regularComplementTopCatMap (2 * Z.regularComplexDimension)
            Z.regularRationalLocallyFiniteFundamentalClass)) := by
  rw [Z.regularGeometricTrace_stage_nativeCompactTrace,
    AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace_eq_pushforward_restriction]
  rfl

/-- The actual compact traces characterize the entire geometric
functional, because every compactly supported cohomology class comes from
a genuine compact-support stage. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_eq_iff_nativeCompactTrace (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (L : Module.Dual ℚ (Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension))) :
    L = Z.regularGeometricTrace ↔
      ∀ (K : Compacts Z.regularAmbientSpace)
        (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
          (2 * Z.regularComplexDimension)),
        L (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
        AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of Z.regularAmbientSpace)
          (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) b
          (AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
            Z.isProperMap_regularComplementTopCatMap (K : Set Z.regularAmbientSpace)
            K.isCompact (2 * Z.regularComplexDimension)
            Z.regularRationalLocallyFiniteFundamentalClass) := by
  constructor
  · rintro rfl K b
    exact Z.regularGeometricTrace_stage_nativeCompactTrace K b
  · intro h
    apply Z.regularGeometricTrace_ext L
    intro K b
    exact (h K b).trans (Z.regularGeometricTrace_stage_nativeCompactTrace K b).symm

end DimensionCycleSupport

end

end OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTraceMeaning
