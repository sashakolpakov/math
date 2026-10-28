import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DeterminantDerivative
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric
import OAI.Analysis.HodgeTheory.Decomposition.MetricPullbackCurve

/-! # Metric Density Derivative -/

namespace OAI.Analysis.HodgeTheory.Decomposition.MetricDensityDerivative.Constructions

noncomputable section

/-! The derivative of the actual metric volume density, obtained from
Jacobi's determinant formula and metric compatibility. -/

variable {E D ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [Fintype ι] [DecidableEq ι]

theorem metricMatrix_infinitesimal_pullback (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix b (MetricPullbackCurve.Constructions.bilinearMetricInfinitesimalPullback B A) =
      (LinearMap.toMatrix b b A.toLinearMap).transpose * AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix b B +
        AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix b B * LinearMap.toMatrix b b A.toLinearMap := by
  ext i j
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix_apply, MetricPullbackCurve.Constructions.bilinearMetricInfinitesimalPullback_apply]
  rw [← b.sum_repr (A (b i)), ← b.sum_repr (A (b j))]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    LinearMap.toMatrix_apply, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem matrix_metric_log_derivative (G A : Matrix ι ι ℝ) (hG : IsUnit G.det) :
    (G⁻¹ * (A.transpose * G + G * A)).trace = 2 * A.trace := by
  rw [Matrix.mul_add, Matrix.trace_add]
  have hfirst : (G⁻¹ * (A.transpose * G)).trace = A.trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
      Matrix.mul_one, Matrix.trace_transpose]
  rw [hfirst, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.one_mul]
  ring

theorem metricMatrix_derivative_rows (b : Module.Basis ι ℝ E)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) {x : D} (hB : DifferentiableAt ℝ B x) (u : D) :
    Matrix.of (fun i => fderiv ℝ (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix b (B y) i) x u) =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix b (fderiv ℝ B x u) := by
  ext i j
  have hr : DifferentiableAt ℝ (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix b (B y) i) x := by
    apply differentiableAt_pi.mpr
    intro k
    exact (hB.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hc := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const (b i) x)).clm_apply
    (hasFDerivAt_const (b j) x)
  have hp := ((ContinuousLinearMap.proj j).hasFDerivAt.comp x hr.hasFDerivAt).fderiv
  simp only [Function.comp_def, ContinuousLinearMap.proj_apply, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix_apply] at hp
  have hv := congrArg (fun L : D →L[ℝ] ℝ => L u) (hp.symm.trans hc.fderiv)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    add_apply, zero_apply, ContinuousLinearMap.comp_zero,
    zero_add, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix_apply, Matrix.of_apply, ContinuousLinearMap.flip_apply] using hv

theorem metricDensity_fderiv_connection (b : Module.Basis ι ℝ E)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) {x : D} (hB : DifferentiableAt ℝ B x)
    (hBs : ∀ v w, B x v w = B x w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v)
    (u : D) (A : E →L[ℝ] E)
    (hA : ∀ v w, B x (A v) w + B x v (A w) = fderiv ℝ B x u v w) :
    fderiv ℝ (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y)) x u =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) * (LinearMap.toMatrix b b A.toLinearMap).trace := by
  have hdet := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix_det_pos b (B x) hBs hpos
  have hr (i : ι) : DifferentiableAt ℝ (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix b (B y) i) x := by
    apply differentiableAt_pi.mpr
    intro j
    exact (hB.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hd : DifferentiableAt ℝ (fun y => (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix b (B y)).det) x := by
    simp only [Matrix.det_apply', AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix_apply]
    fun_prop
  have hT : fderiv ℝ B x u = MetricPullbackCurve.Constructions.bilinearMetricInfinitesimalPullback (B x) A := by
    ext v w
    exact (hA v w).symm
  have hJac := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DeterminantDerivative.CM.Construction.determinant_derivative_trace (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricMatrix b (B y)) hr
    (isUnit_iff_ne_zero.mpr hdet.ne') u
  rw [metricMatrix_derivative_rows b B hB, hT, metricMatrix_infinitesimal_pullback,
    matrix_metric_log_derivative _ _ (isUnit_iff_ne_zero.mpr hdet.ne')] at hJac
  have hs := congrArg (fun L : D →L[ℝ] ℝ => L u) (hd.hasFDerivAt.sqrt hdet.ne').fderiv
  change fderiv ℝ (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y)) x u = _ at hs
  rw [smul_apply, smul_eq_mul, hJac] at hs
  rw [hs]
  have hsq := Real.sq_sqrt hdet.le
  have hne := (Real.sqrt_pos.mpr hdet).ne'
  unfold AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity
  field_simp
  rw [hsq]

end

end OAI.Analysis.HodgeTheory.Decomposition.MetricDensityDerivative.Constructions
