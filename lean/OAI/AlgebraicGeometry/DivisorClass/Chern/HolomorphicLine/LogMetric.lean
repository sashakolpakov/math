import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.HermitianPair
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Log Metric -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.LogMetric

noncomputable section

/-! Smooth logarithmic metric potentials and their exact transition law. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)

def holomorphicLineLogMetric (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) : ℝ :=
  Real.log (MetricWeight.holomorphicLineMetricWeight u i x)

theorem holomorphicLineLogMetric_transition (i j x : M)
    (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (hj : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j) :
    holomorphicLineLogMetric u i ⟨x, hi⟩ =
      Real.log (Complex.normSq ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩)) +
        holomorphicLineLogMetric u j ⟨x, hj⟩ := by
  unfold holomorphicLineLogMetric
  rw [MetricWeight.holomorphicLineMetricWeight_transition u i j x hi hj]
  exact Real.log_mul (ne_of_gt (Complex.normSq_pos.mpr
    (Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j) ⟨x, hi, hj⟩)))
      (ne_of_gt (MetricWeight.holomorphicLineMetricWeight_pos u j ⟨x, hj⟩))

variable [IsScalarTower ℝ ℂ E]

theorem holomorphicLineLogMetric_contMDiff (i : M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (holomorphicLineLogMetric u i) := by
  intro x
  exact (Real.contDiffAt_log.mpr (ne_of_gt (MetricWeight.holomorphicLineMetricWeight_pos u i x))).contMDiffAt.comp x
    (HermitianPair.holomorphicLineMetricWeight_contMDiff u i x)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.LogMetric
