import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOpenConnection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureOverlap

/-! # Connection Logs -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ConnectionLogs

noncomputable section

/-! The original metric connections differ by the derivative of an actual holomorphic transition logarithm. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [T2Space M]
  [IsManifold 𝓘(ℂ, E) ∞ M] (u : Connecting.holomorphicUnitCohomology E M)

theorem holomorphicLineLocalConnectionForm_eq_scalar (i : M) :
    HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u i = ScalarOpenConnection.smoothScalarOpenConnection (HolomorphicLine.LocalCurvature.holomorphicLineLogMetricFunction u i) := rfl

theorem holomorphicLineLocalConnectionForm_log_overlap (i j : M) (W : Opens M)
    (hW : W ≤ CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u j)
    (l : Exponential.HolomorphicFunction (E := E) (M := W))
    (hl : ∀ x : W, (CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x.val, hW x.property⟩ = Complex.exp (l x)) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hW.trans inf_le_left) (HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u i) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hW.trans inf_le_right) (HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u j) +
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l)) := by
  rw [holomorphicLineLocalConnectionForm_eq_scalar, holomorphicLineLocalConnectionForm_eq_scalar,
    ScalarOpenConnection.smoothScalarOpenConnection_restrict, ScalarOpenConnection.smoothScalarOpenConnection_restrict]
  apply ScalarOpenConnection.smoothScalarOpenConnection_log_difference l
  intro x
  change (HolomorphicLine.LogMetric.holomorphicLineLogMetric u i ⟨x.val, (hW x.property).1⟩ : ℂ) -
    (HolomorphicLine.LogMetric.holomorphicLineLogMetric u j ⟨x.val, (hW x.property).2⟩ : ℂ) = _
  rw [HolomorphicLine.LogMetric.holomorphicLineLogMetric_transition u i j x.val (hW x.property).1 (hW x.property).2,
    Complex.ofReal_add, add_sub_cancel_right, hl x]

theorem holomorphicLineLocalConnectionForm_exists_log_overlap (i j : M)
    (x : ↥(CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u j)) :
    ∃ (W : Opens M) (hW : W ≤ CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u j),
      x.val ∈ W ∧ ∃ l : Exponential.HolomorphicFunction (E := E) (M := W),
        (∀ y : W, (CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨y.val, hW y.property⟩ = Complex.exp (l y)) ∧
          Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hW.trans inf_le_left) (HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u i) =
            Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hW.trans inf_le_right) (HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u j) +
              Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l)) := by
  obtain ⟨W, hW, hx, l, hl⟩ := ExponentialEpi.exists_holomorphicSubopenLog (CohomologyTransitions.holomorphicCohomologyTransition E M u i j) x
  exact ⟨W, hW, hx, l, fun y => (hl y).symm,
    holomorphicLineLocalConnectionForm_log_overlap u i j W hW l (fun y => (hl y).symm)⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ConnectionLogs
