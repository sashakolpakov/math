import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Cocycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureIntegration

/-! # Integration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! Integration of any actual metric curvature gives the original rational Chern class. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] [CompactSpace M] [T2Space M] {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}

theorem Data.HolomorphicLineMetricData.curvature_smooth_chern (h : Data.HolomorphicLineMetricData u) :
    HomologicalComplex.homologyMap (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) 2
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 h.curvatureCocycle) =
    ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap (ComplexMultiplication.HodgeComparison.RationalSmoothCech.CM.Construction.rationalSmoothCochainMap E M) 2 (Holomorphic.Singular.holomorphicFirstChernClassQ E M u) :=
  (congrArg (HomologicalComplex.homologyMap (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) 2)
    h.curvature_class_original).trans (Holomorphic.CurvatureIntegration.holomorphicLine_curvature_smooth_chern u)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
