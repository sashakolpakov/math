import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Geometry.Manifold.Metrizable

/-! # Open Paracompact -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.OpenParacompact

noncomputable section

/-!
# Paracompactness of actual open subspaces

Metrizable spaces have paracompact open subspaces. Mathlib's metrizability
result supplies this property for finite-dimensional sigma-compact
Hausdorff manifolds, without assuming it as additional geometric data.
-/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every actual open subspace of a metrizable space is paracompact. -/
theorem paracompactSpace_open_of_metrizable (X : TopCat.{0})
    [MetrizableSpace X] (U : Opens X) : ParacompactSpace U := by
  let : MetricSpace X := metrizableSpaceMetric X
  exact inferInstanceAs (ParacompactSpace (U : Set X))

/-- The open-subspace condition follows for finite-dimensional,
sigma-compact Hausdorff manifolds from the proved metrizability theorem. -/
theorem paracompactSpace_open_of_chartedSpace
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : TopCat.{0}) [ChartedSpace E X] [SigmaCompactSpace X] [T2Space X]
    (U : Opens X) : ParacompactSpace U := by
  have : MetrizableSpace X := Manifold.metrizableSpace 𝓘(ℝ, E) X
  exact paracompactSpace_open_of_metrizable X U

end

end OAI.AlgebraicTopology.Cohomology.Singular.OpenParacompact
