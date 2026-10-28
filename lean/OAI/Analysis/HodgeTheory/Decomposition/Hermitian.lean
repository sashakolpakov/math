import OAI.Analysis.HodgeTheory.Decomposition.KahlerMetric

/-! # Hermitian -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Hermitian.Constructions

noncomputable section

/-! Hermitian tangent pairings derived from the actual projective Kähler metric.
The inner-product core is retained as data, so the analytic model's existing norm
and manifold topology are not replaced by another typeclass instance. -/

open scoped ContDiff _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

theorem metricHermitianPair_add_left (B : E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    KahlerMetric.Constructions.metricHermitianPair B (u + v) w = KahlerMetric.Constructions.metricHermitianPair B u w + KahlerMetric.Constructions.metricHermitianPair B v w := by
  simp only [KahlerMetric.Constructions.metricHermitianPair, map_add, add_apply, Complex.ofReal_add]
  ring

theorem metricHermitianPair_zero_left (B : E →L[ℝ] E →L[ℝ] ℝ) (u : E) :
    KahlerMetric.Constructions.metricHermitianPair B 0 u = 0 := by
  simp [KahlerMetric.Constructions.metricHermitianPair]

/-- Conjugate linearity in the first argument follows from the proved symmetry. -/
theorem projectiveMetricHermitian_smul_left (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (u v : V.analyticModel) (z : ℂ) :
    KahlerMetric.Constructions.metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y) (z • u) v =
      star z * KahlerMetric.Constructions.metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y) u v := by
  rw [KahlerMetric.Constructions.projectiveMetricHermitian_symm V e he y hy v (z • u),
    KahlerMetric.Constructions.metricHermitianPair_smul_right, star_mul,
    ← KahlerMetric.Constructions.projectiveMetricHermitian_symm V e he y hy v u]
  exact mul_comm _ _

/-- Every tangent-coordinate fiber has a positive definite Hermitian inner product
constructed from the projective metric, with no added geometric hypothesis. -/
@[instance_reducible] def projectiveHermitianCore (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) :
    InnerProductSpace.Core ℂ V.analyticModel where
  inner := KahlerMetric.Constructions.metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y)
  conj_inner_symm u v := by
    change star (KahlerMetric.Constructions.metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y) v u) = _
    simpa only [star_star] using congrArg star (KahlerMetric.Constructions.projectiveMetricHermitian_symm V e he y hy u v)
  add_left := metricHermitianPair_add_left _
  smul_left := fun u v z => projectiveMetricHermitian_smul_left V e he y hy u v z
  re_inner_nonneg u := by
    by_cases hu : u = 0
    · subst u
      simp only [metricHermitianPair_zero_left, map_zero, le_refl]
    · exact (KahlerMetric.Constructions.projectiveMetricHermitian_positive V e he y hy u hu).le
  definite u hu := by
    by_contra hne
    have hp := KahlerMetric.Constructions.projectiveMetricHermitian_positive V e he y hy u hne
    rw [hu, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp

/-- Fixed-vector coefficients of the Hermitian metric are smooth in each chart. -/
theorem projectiveMetricHermitian_smooth (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (u v : V.analyticModel) :
    ContDiffOn ℝ ∞ (fun y => KahlerMetric.Constructions.metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y) u v) e.target := by
  have hB := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_smooth V e he
  have hv := (hB.clm_apply (contDiffOn_const (c := u))).clm_apply (contDiffOn_const (c := v))
  have hJv := (hB.clm_apply (contDiffOn_const (c := u))).clm_apply
    (contDiffOn_const (c := Complex.I • v))
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hv).sub
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hJv))

/-- The Hermitian pairing has the same coordinate-change law as the real metric. -/
theorem projectiveMetricHermitian_transition (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {y : V.analyticModel} (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source)
    (u v : V.analyticModel) :
    KahlerMetric.Constructions.metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y) u v =
      KahlerMetric.Constructions.metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V f (f (e.symm y)))
        (fderiv ℂ (f ∘ e.symm) y u) (fderiv ℂ (f ∘ e.symm) y v) := by
  have hhol := (DifferentialForms.Manifold.ComplexCharts.complexContDiffAt_chart_transition e f he hf hy hfy).differentiableAt (by simp)
  unfold KahlerMetric.Constructions.metricHermitianPair
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_transition V e f he hf hy hfy u v,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_transition V e f he hf hy hfy u (Complex.I • v),
    hhol.fderiv_restrictScalars ℝ]
  change (_ : ℂ) - Complex.I *
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V f (f (e.symm y))
      (fderiv ℂ (f ∘ e.symm) y u) (fderiv ℂ (f ∘ e.symm) y (Complex.I • v)) : ℂ) = _
  rw [(fderiv ℂ (f ∘ e.symm) y).map_smul]
  rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.Hermitian.Constructions
