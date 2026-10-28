import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Curvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ConnectionLogs
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Change

/-! # Connection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! Actual local Chern connection forms for every constructed Hermitian metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} (h : Data.HolomorphicLineMetricData u)

def Data.HolomorphicLineMetricData.localConnection (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) 1 :=
  ScalarOpenConnection.smoothScalarOpenConnection (h.logFunction i)

theorem Data.HolomorphicLineMetricData.localConnection_d (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (h.localConnection i) = h.localCurvature i := rfl

theorem Connection.scalarConnection_global_onOpen
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) (⊤ : Opens M)) (U : Opens M) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (ScalarOpenConnection.smoothScalarOpenConnection f)) =
      ScalarOpenConnection.smoothScalarOpenConnection (SmoothScalarForm.smoothComplexOpenFunctionRestrict le_top f) := by
  have he : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (ScalarOpenConnection.smoothScalarOpenConnection f)) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict le_top (ScalarOpenConnection.smoothScalarOpenConnection f) :=
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.restrict_onOpen (show U ≤ (⊤ : Opens M) from le_top) _).symm.trans
      (congrArg (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show U ≤ (⊤ : Opens M) from le_top))
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.onOpen_toGlobal (ScalarOpenConnection.smoothScalarOpenConnection f)))
  exact he.trans (ScalarOpenConnection.smoothScalarOpenConnection_restrict le_top f)

theorem Data.HolomorphicLineMetricData.localConnection_change (k : Data.HolomorphicLineMetricData u) (i : M) :
    h.localConnection i = k.localConnection i +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (h.changePrimitive k) := by
  unfold Data.HolomorphicLineMetricData.localConnection
  rw [h.logFunction_ratio k i, ScalarOpenConnection.smoothScalarOpenConnection_add]
  exact congrArg (fun a => ScalarOpenConnection.smoothScalarOpenConnection (k.logFunction i) + a)
    (Connection.scalarConnection_global_onOpen (h.ratioLogFunction k) (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)).symm

theorem Data.HolomorphicLineMetricData.localConnection_log_overlap (i j : M) (W : Opens M)
    (hW : W ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)
    (l : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := W))
    (hl : ∀ x : W, (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x.val, hW x.property⟩ = Complex.exp (l x)) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hW.trans inf_le_left) (h.localConnection i) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hW.trans inf_le_right) (h.localConnection j) +
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l)) := by
  rw [Data.HolomorphicLineMetricData.localConnection, Data.HolomorphicLineMetricData.localConnection,
    ScalarOpenConnection.smoothScalarOpenConnection_restrict, ScalarOpenConnection.smoothScalarOpenConnection_restrict]
  apply ScalarOpenConnection.smoothScalarOpenConnection_log_difference l
  intro x
  change h.logFunction i ⟨x.val, (hW x.property).1⟩ - h.logFunction j ⟨x.val, (hW x.property).2⟩ = _
  rw [h.logFunction_transition i j x.val (hW x.property).1 (hW x.property).2, hl x]

theorem Data.HolomorphicLineMetricData.localConnection_exists_log_overlap (i j : M)
    (x : ↥(Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)) :
    ∃ (W : Opens M) (hW : W ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j),
      x.val ∈ W ∧ ∃ l : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := W),
        (∀ y : W, (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨y.val, hW y.property⟩ = Complex.exp (l y)) ∧
          Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hW.trans inf_le_left) (h.localConnection i) =
            Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hW.trans inf_le_right) (h.localConnection j) +
              Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l)) := by
  obtain ⟨W, hW, hx, l, hl⟩ := Holomorphic.ExponentialEpi.exists_holomorphicSubopenLog (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j) x
  exact ⟨W, hW, hx, l, fun y => (hl y).symm,
    h.localConnection_log_overlap i j W hW l (fun y => (hl y).symm)⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
