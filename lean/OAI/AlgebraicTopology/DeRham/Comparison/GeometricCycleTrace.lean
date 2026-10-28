import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularCycleFundamentalClass
import OAI.AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback
import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit

/-! # Geometric Cycle Trace -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTrace.DimensionCycleSupport

noncomputable section

/-!
# The geometric trace of an actual algebraic regular locus

After removing the singular boundary, the actual regular locus is a closed
complex submanifold of the ambient open set. Proper pullback of compactly
supported cohomology followed by its canonical top trace gives a genuine
rational functional. At every compact support this is explicitly evaluation
on the constructed integral fundamental class of the inverse compact set.

This definition does not use the supported Thom class or the existing
algebraic cycle-class map.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

variable {V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The degree complementary to the cycle's degree is the actual top
degree of its nonempty smooth regular locus. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_degree (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (p + p) + 2 * Z.regularComplexDimension = 2 * V.complexDimension := by
  have h := Z.regularComplexDimension_add_codimension
  omega

/-- Genuine proper pullback to the regular locus, followed by its actual
top-degree trace. The regular inclusion is proper in the singular-boundary
complement, without assuming that the regular locus is compact. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Module.Dual ℚ (Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension)) :=
  (Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := Z.regularAnalyticSpace)).hom.comp
    (Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap
      (2 * Z.regularComplexDimension)).hom

/-- The functional has precisely the proper-pullback and top-trace meaning
stated in its definition. -/
@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_apply (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (b : Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension)) :
    Z.regularGeometricTrace b =
      Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := Z.regularAnalyticSpace)
        (Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
          Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap
          (2 * Z.regularComplexDimension) b) := rfl

/-- At a compact support, the geometric trace evaluates the actual
relative pullback on the integral compact fundamental class of the
inverse compact subset of the regular locus. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_stage (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (K : Compacts Z.regularAmbientSpace)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      (2 * Z.regularComplexDimension)) :
    Z.regularGeometricTrace
        (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
      Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of Z.regularAnalyticSpace)
        ((Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage Z.regularComplementTopCatMap
          Z.isProperMap_regularComplementTopCatMap K :
            Compacts Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace)ᶜ
        (2 * Z.regularComplexDimension)
        (Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
          Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K
          (2 * Z.regularComplexDimension) b)
        (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass Z.regularComplexDimension
          (Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage Z.regularComplementTopCatMap
            Z.isProperMap_regularComplementTopCatMap K : Set Z.regularAnalyticSpace)
          (Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage Z.regularComplementTopCatMap
            Z.isProperMap_regularComplementTopCatMap K).isCompact) := by
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_apply]
  have h := ConcreteCategory.congr_hom
    (Duality.Poincare.ProperCompactSupportPullback.compactSupportCohomologyι_properPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K
      (2 * Z.regularComplexDimension)) b
  change Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap
      (2 * Z.regularComplexDimension)
      (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
        (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) = _ at h
  rw [h]
  exact Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_stage_apply Z.regularComplexDimension
    (Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage Z.regularComplementTopCatMap
      Z.isProperMap_regularComplementTopCatMap K) _

/-- Testing all compact-support stages tests the entire geometric
functional, by the proved compact-support colimit. No decomposition into
coordinate-chart cohomology classes is assumed. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_ext (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (L : Module.Dual ℚ (Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension)))
    (h : ∀ (K : Compacts Z.regularAmbientSpace)
      (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
        (2 * Z.regularComplexDimension)),
      L (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
        Z.regularGeometricTrace
          (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
            (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b)) :
    L = Z.regularGeometricTrace := by
  apply LinearMap.ext
  intro b
  obtain ⟨K, c, rfl⟩ := Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension) b
  exact h K c

end

end OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTrace.DimensionCycleSupport
