import OAI.Analysis.HodgeTheory.Decomposition.CovectorMetricDifferential
import OAI.Analysis.HodgeTheory.Decomposition.MetricDensityDerivative
import OAI.Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra

/-! # Weighted Metric Derivative -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeightedMetricDerivative.Constructions

noncomputable section

/-! Differentiation of the actual density-weighted covector metric, including
the connection action on a constant test covector. -/

open scoped ContDiff

attribute [local instance] BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace
  BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [FiniteDimensional ℝ E] in
theorem bilinearFormMetricPair_differentiableAt (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (a c : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (hB : DifferentiableAt ℝ B x) (ha : DifferentiableAt ℝ a x) (hc : DifferentiableAt ℝ c x)
    (hdet : (BilinearFormMetric.Constructions.bilinearExteriorGram b n (B x)).det ≠ 0) :
    DifferentiableAt ℝ (fun y => BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B y) (a y) (c y)) x := by
  have hF := (BilinearFormMetricSmooth.Constructions.bilinearFormMetricPair_joint_contDiffAt b n (B x) (a x) (c x) hdet).differentiableAt (by simp)
  have h := hF.hasFDerivAt.comp x (hB.hasFDerivAt.prodMk (ha.hasFDerivAt.prodMk hc.hasFDerivAt))
  exact h.differentiableAt

theorem weightedMetricPair_derivative (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (c : DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (u : E)
    (hB : DifferentiableAt ℝ B x) (ha : DifferentiableAt ℝ a x)
    (hρ : DifferentiableAt ℝ (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y)) x)
    (hBs : ∀ v w, B x v w = B x w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hΓ : ∀ v w, B x (Γ x u v) w + B x v (Γ x u w) = fderiv ℝ B x u v w) :
    fderiv ℝ (fun y => (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) * BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B y) (a y) c) x u =
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) *
        (BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (CovectorConnection.Constructions.covectorConnectionDerivative n Γ a x u) c -
          BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (a x) (CovectorConnection.Constructions.covectorInfinitesimalAction n (Γ x u) c) +
            (LinearMap.toMatrix b b (Γ x u).toLinearMap).trace • BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (a x) c) := by
  have hp := bilinearFormMetricPair_differentiableAt b n B a (fun _ => c) hB ha
    (differentiableAt_const c) (BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) hBs hpos)
  have hρc := Complex.ofRealCLM.hasFDerivAt.comp x hρ.hasFDerivAt
  have hd := congrArg (fun L : E →L[ℝ] ℂ => L u) (hρc.mul hp.hasFDerivAt).fderiv
  have hmetric := CovectorMetricDifferential.Constructions.bilinearFormMetricPair_covariant_derivative b n B Γ a (fun _ => c) x u
    hB ha (differentiableAt_const c) hBs hpos hΓ
  have hconst : CovectorConnection.Constructions.covectorConnectionDerivative n Γ (fun _ => c) x u =
      -CovectorConnection.Constructions.covectorInfinitesimalAction n (Γ x u) c := by
    rw [CovectorConnection.Constructions.covectorConnectionDerivative_apply, (hasFDerivAt_const c x).fderiv, zero_apply, zero_sub]
  rw [hconst, BilinearPairAlgebra.Constructions.bilinearFormMetricPair_neg_right] at hmetric
  have hvolume := MetricDensityDerivative.Constructions.metricDensity_fderiv_connection b B hB hBs hpos u (Γ x u) hΓ
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_eq_mul] at hd
  rw [hmetric, hvolume] at hd
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at hd
  change fderiv ℝ (fun y => (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) * BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B y) (a y) c) x u = _ at hd
  rw [hd]
  simp only [Complex.ofReal_mul, RCLike.real_smul_eq_coe_mul]
  ring_nf
  rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.WeightedMetricDerivative.Constructions
