import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Connection
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarExterior

/-! # Metric Connection Reality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Metric compatibility of the actual local Chern connection, with its original positive weight. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {U : Opens M}

theorem MetricConnectionReality.smoothScalarOpenConnection_add_conjugate (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (hf : ∀ x : U, conj (f x) = f x) :
    ScalarOpenConnection.smoothScalarOpenConnection f + Open.ConjugateForms.openManifoldConjugate (ScalarOpenConnection.smoothScalarOpenConnection f) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f) := by
  have hF : Open.ConjugateForms.openManifoldConjugate (SmoothScalarForm.smoothScalarOpenZeroForm f) = SmoothScalarForm.smoothScalarOpenZeroForm f := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    ext v
    rw [Open.ConjugateForms.openManifoldConjugate_apply, SmoothScalarForm.smoothScalarOpenZeroForm_apply]
    exact hf x
  have hdF : Open.ConjugateForms.openManifoldConjugate (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f) := by
    rw [← Open.ConjugateForms.openManifoldConjugate_d, hF]
  have hI : conj (-Complex.I) = Complex.I := by apply Complex.ext <;> norm_num
  rw [ScalarOpenConnection.smoothScalarOpenConnection, Open.ConjugateProjection.openManifoldConjugate_onePart, hI, hdF]
  exact Manifold.OneFormProjection.openManifoldOnePart_add _

variable {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

def HolomorphicMetric.Data.HolomorphicLineMetricData.weightFunction (i : M) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :=
  ⟨fun x => (h.weight i x : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp (h.smooth i)⟩

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightFunction_exp_log (i : M) :
    h.weightFunction i = SmoothScalarExterior.smoothComplexOpenFunctionExp (h.logFunction i) := by
  apply ContMDiffMap.ext
  intro x
  change (h.weight i x : ℂ) = Complex.exp (Real.log (h.weight i x) : ℂ)
  rw [← Complex.ofReal_exp, Real.exp_log (h.positive i x)]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.localConnection_add_conjugate (i : M) :
    h.localConnection i + Open.ConjugateForms.openManifoldConjugate (h.localConnection i) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (h.logFunction i)) :=
  MetricConnectionReality.smoothScalarOpenConnection_add_conjugate (h.logFunction i) (fun _ => Complex.conj_ofReal _)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightFunction_d (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (h.weightFunction i)) =
      SmoothScalarForm.smoothScalarOpenFormMul (h.weightFunction i)
        (h.localConnection i + Open.ConjugateForms.openManifoldConjugate (h.localConnection i)) := by
  rw [h.localConnection_add_conjugate, h.weightFunction_exp_log]
  exact SmoothScalarExterior.smoothScalarOpenZeroForm_d_exp (h.logFunction i)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
