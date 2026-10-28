import OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth
import OAI.Analysis.HodgeTheory.Decomposition.MetricPullbackCurve

/-! # Bilinear Metric Differential -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions

noncomputable section

/-! The derivative of the induced form metric vanishes on the simultaneous
infinitesimal pullback of the metric and its two covector arguments. -/

open scoped ContDiff

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

local instance metricDifferentialBilinearNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricDifferentialBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricDifferentialCovectorPairNormedSpace (n : ℕ) :
    NormedSpace ℝ (DifferentialForms.Manifold.Basic.FormValue E n × DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance

def bilinearFormMetricDifferential (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : DifferentialForms.Manifold.Basic.FormValue E n) :
    ((E →L[ℝ] E →L[ℝ] ℝ) × DifferentialForms.Manifold.Basic.FormValue E n × DifferentialForms.Manifold.Basic.FormValue E n) →L[ℝ] ℂ :=
  fderiv ℝ (fun x : (E →L[ℝ] E →L[ℝ] ℝ) × DifferentialForms.Manifold.Basic.FormValue E n × DifferentialForms.Manifold.Basic.FormValue E n =>
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n x.1 x.2.1 x.2.2) (B, a, c)

theorem bilinearFormMetricDifferential_pullback (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (A : E →L[ℝ] E) (a c : DifferentialForms.Manifold.Basic.FormValue E n) :
    bilinearFormMetricDifferential b n B a c
      (MetricPullbackCurve.Constructions.bilinearMetricInfinitesimalPullback B A, CovectorConnection.Constructions.covectorInfinitesimalAction n A a, CovectorConnection.Constructions.covectorInfinitesimalAction n A c) = 0 := by
  let P := fun t =>
    (MetricPullbackCurve.Constructions.bilinearMetricPullback B (MetricPullbackCurve.Constructions.tangentLinearPerturbation A t),
      a.compContinuousLinearMap (MetricPullbackCurve.Constructions.tangentLinearPerturbation A t),
      c.compContinuousLinearMap (MetricPullbackCurve.Constructions.tangentLinearPerturbation A t))
  have hP : HasDerivAt P
      (MetricPullbackCurve.Constructions.bilinearMetricInfinitesimalPullback B A, CovectorConnection.Constructions.covectorInfinitesimalAction n A a, CovectorConnection.Constructions.covectorInfinitesimalAction n A c) 0 :=
    (MetricPullbackCurve.Constructions.bilinearMetricPullback_hasDerivAt B A).prodMk
      ((MetricPullbackCurve.Constructions.covectorPullback_hasDerivAt n A a).prodMk (MetricPullbackCurve.Constructions.covectorPullback_hasDerivAt n A c))
  have hP0 : P 0 = (B, a, c) := by
    simp only [P, MetricPullbackCurve.Constructions.tangentLinearPerturbation_zero, MetricPullbackCurve.Constructions.bilinearMetricPullback_id]
    apply Prod.ext rfl
    apply Prod.ext <;> ext v <;> rfl
  let F := fun x : (E →L[ℝ] E →L[ℝ] ℝ) × DifferentialForms.Manifold.Basic.FormValue E n × DifferentialForms.Manifold.Basic.FormValue E n =>
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n x.1 x.2.1 x.2.2
  have hF : DifferentiableAt ℝ F (B, a, c) :=
    (BilinearFormMetricSmooth.Constructions.bilinearFormMetricPair_joint_contDiffAt b n B a c (BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n B hB hpos)).differentiableAt (by simp)
  have hchain := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hP hP0.symm
  have hconst : HasDerivAt (F ∘ P) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (F (B, a, c))).congr_of_eventuallyEq
      (MetricPullbackCurve.Constructions.bilinearFormMetricPair_pullback_curve b n B hB hpos A a c)
  exact hchain.unique hconst

end

end OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions
