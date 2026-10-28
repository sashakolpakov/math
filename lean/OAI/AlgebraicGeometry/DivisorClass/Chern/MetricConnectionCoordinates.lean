import OAI.AlgebraicGeometry.DivisorClass.Chern.MetricConnectionReality
import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormCoordinates

/-! # Metric Connection Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original positive weight and local Chern connection satisfy the exact coordinate metric equation. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {U : Opens M} {n : ℕ}

theorem MetricConnectionCoordinates.openManifoldConjugate_inChart (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (e : OpenPartialHomeomorph M E) {y : E} (hy : e.symm y ∈ U) (v : Fin n → E) :
    (Open.ConjugateForms.openManifoldConjugate a).extension.inChart e y v = conj (a.extension.inChart e y v) := by
  unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply a ⟨e.symm y, hy⟩]
  exact Open.ConjugateForms.openManifoldConjugate_apply a ⟨e.symm y, hy⟩ _

end

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightFunction_chart_derivative (i : M)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)) (v : E) :
    fderiv ℝ (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (h.weightFunction i) ∘ e.symm) y v =
      Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (h.weightFunction i) (e.symm y) *
        (conj (AntiOneFormCoordinates.oneFormLinear ((h.localConnection i).extension.inChart e y) v) +
          AntiOneFormCoordinates.oneFormLinear ((h.localConnection i).extension.inChart e y) v) := by
  have hp := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) 1 =>
    a.extension.inChart e y (fun _ => v)) (h.weightFunction_d i)
  rw [SmoothScalarExterior.smoothScalarOpenZeroForm_d_inChart _ e he hy,
    SmoothScalarForm.smoothScalarOpenFormMul_inChart _ _ e hy.2,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Pi.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
    MetricConnectionCoordinates.openManifoldConjugate_inChart _ e hy.2] at hp
  change fderiv ℝ (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (h.weightFunction i) ∘ e.symm) y v =
    Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (h.weightFunction i) (e.symm y) *
      (AntiOneFormCoordinates.oneFormLinear ((h.localConnection i).extension.inChart e y) v +
        conj (AntiOneFormCoordinates.oneFormLinear ((h.localConnection i).extension.inChart e y) v)) at hp
  exact hp.trans (congrArg (fun z => Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)
    (h.weightFunction i) (e.symm y) * z) (add_comm _ _))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
