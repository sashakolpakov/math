import OAI.Analysis.HodgeTheory.Decomposition.ExteriorPair

/-! # Projective Form Metric -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions

noncomputable section

/-! Pointwise form metrics on the genuine projective manifold. Chart changes
are isometries for the constructed metric, so the resulting pairing is global. -/

open scoped _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

/-- Scalar restriction for the equivalence between the two different normed fibers. -/
def projectiveMetricFiberRealEquiv
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) :
    MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy ≃L[ℝ] V.analyticModel where
  toLinearEquiv := (MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).toLinearEquiv.restrictScalars ℝ
  continuous_toFun := (MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).continuous
  continuous_invFun := (MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).symm.continuous

theorem projectiveMetricFiber_real_inner
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target)
    (u v : MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) :
    inner ℝ u v = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y
      (MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy u) (MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy v) := by
  change (inner ℂ u v).re = _
  rw [MetricFiber.Constructions.projectiveMetricFiber_inner]
  simp [KahlerMetric.Constructions.metricHermitianPair]

def metricChartTransition
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    (x : V.analyticSpace) (hex : x ∈ e.source) (hfx : x ∈ f.source) :
    MetricFiber.Constructions.ProjectiveMetricFiber V e he (e x) (e.map_source hex) ≃L[ℝ]
      MetricFiber.Constructions.ProjectiveMetricFiber V f hf (f x) (f.map_source hfx) :=
  (projectiveMetricFiberRealEquiv V e he (e x) (e.map_source hex)).trans
    (((DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hex).symm.trans (DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv f hf x hfx)).trans
      (projectiveMetricFiberRealEquiv V f hf (f x) (f.map_source hfx)).symm)

theorem metricChartTransition_apply
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    (x : V.analyticSpace) (hex : x ∈ e.source) (hfx : x ∈ f.source)
    (u : MetricFiber.Constructions.ProjectiveMetricFiber V e he (e x) (e.map_source hex)) :
    MetricFiber.Constructions.projectiveMetricFiberEquiv V f hf (f x) (f.map_source hfx)
      (metricChartTransition V e f he hf x hex hfx u) =
      fderiv ℝ (f ∘ e.symm) (e x)
        (MetricFiber.Constructions.projectiveMetricFiberEquiv V e he (e x) (e.map_source hex) u) := by
  have hfx' : e.symm (e x) ∈ f.source := by rwa [e.left_inv hex]
  rw [DifferentialForms.Manifold.Charts.fderiv_chart_transition e f he hf (e.map_source hex) hfx', e.left_inv hex]
  rfl

/-- The actual transition derivative between two metric tangent fibers is an isometry. -/
def metricChartIsometry
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    (x : V.analyticSpace) (hex : x ∈ e.source) (hfx : x ∈ f.source) :
    MetricFiber.Constructions.ProjectiveMetricFiber V e he (e x) (e.map_source hex) ≃ₗᵢ[ℝ]
      MetricFiber.Constructions.ProjectiveMetricFiber V f hf (f x) (f.map_source hfx) :=
  (metricChartTransition V e f he hf x hex hfx).toLinearEquiv.isometryOfInner (by
    intro u v
    rw [projectiveMetricFiber_real_inner, projectiveMetricFiber_real_inner]
    change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V f (f x)
      (MetricFiber.Constructions.projectiveMetricFiberEquiv V f hf (f x) (f.map_source hfx)
        (metricChartTransition V e f he hf x hex hfx u))
      (MetricFiber.Constructions.projectiveMetricFiberEquiv V f hf (f x) (f.map_source hfx)
        (metricChartTransition V e f he hf x hex hfx v)) = _
    rw [metricChartTransition_apply, metricChartTransition_apply]
    have hfx' : e.symm (e x) ∈ f.source := by rwa [e.left_inv hex]
    simpa only [e.left_inv hex] using
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_transition V e f he hf (e.map_source hex) hfx'
        (MetricFiber.Constructions.projectiveMetricFiberEquiv V e he (e x) (e.map_source hex) u)
        (MetricFiber.Constructions.projectiveMetricFiberEquiv V e he (e x) (e.map_source hex) v)).symm)

/-- A genuine coordinate form transported to its metric tangent fiber. -/
def metricCoordinateForm
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (n : ℕ) (form : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n) :
    DifferentialForms.Manifold.Basic.FormValue (MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) n :=
  form.compContinuousLinearMap
    ((MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).toContinuousLinearMap.restrictScalars ℝ)

def projectiveChartFormPair
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (n : ℕ) (a b : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n) : ℂ :=
  ExteriorPair.Constructions.formMetricPair n (metricCoordinateForm V e he y hy n a) (metricCoordinateForm V e he y hy n b)

theorem metricCoordinateForm_transition
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    (x : V.analyticSpace) (hex : x ∈ e.source) (hfx : x ∈ f.source)
    (n : ℕ) (form : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) :
    metricCoordinateForm V e he (e x) (e.map_source hex) n (form.inChart e (e x)) =
      (metricCoordinateForm V f hf (f x) (f.map_source hfx) n (form.inChart f (f x))).compContinuousLinearMap
        (metricChartIsometry V e f he hf x hex hfx).toContinuousLinearEquiv.toContinuousLinearMap := by
  have hfx' : e.symm (e x) ∈ f.source := by rwa [e.left_inv hex]
  rw [form.inChart_transition e f he hf (e.map_source hex) hfx', e.left_inv hex]
  ext v
  change form.inChart f (f x)
    (fun i => fderiv ℝ (f ∘ e.symm) (e x)
      (MetricFiber.Constructions.projectiveMetricFiberEquiv V e he (e x) (e.map_source hex) (v i))) =
    form.inChart f (f x)
    (fun i => MetricFiber.Constructions.projectiveMetricFiberEquiv V f hf (f x) (f.map_source hfx)
      (metricChartTransition V e f he hf x hex hfx (v i)))
  simp only [metricChartTransition_apply]

/-- The pointwise pairing computed in any two charts at a point agrees. -/
theorem projectiveChartFormPair_transition
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    (x : V.analyticSpace) (hex : x ∈ e.source) (hfx : x ∈ f.source)
    (n : ℕ) (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) :
    projectiveChartFormPair V e he (e x) (e.map_source hex) n (a.inChart e (e x)) (b.inChart e (e x)) =
      projectiveChartFormPair V f hf (f x) (f.map_source hfx) n (a.inChart f (f x)) (b.inChart f (f x)) := by
  unfold projectiveChartFormPair
  rw [metricCoordinateForm_transition V e f he hf x hex hfx n a,
    metricCoordinateForm_transition V e f he hf x hex hfx n b, ExteriorPair.Constructions.formMetricPair_pullback]

theorem metricCoordinateForm_injective
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (n : ℕ) :
    Function.Injective (metricCoordinateForm V e he y hy n) := by
  intro a b hab
  ext v
  have h := congrArg (fun form : DifferentialForms.Manifold.Basic.FormValue (MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) n =>
    form (fun i => (MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).symm (v i))) hab
  change a (fun i => MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy
    ((MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).symm (v i))) =
    b (fun i => MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy
    ((MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).symm (v i))) at h
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

theorem metricCoordinateForm_zero
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (n : ℕ) :
    metricCoordinateForm V e he y hy n 0 = 0 := by ext v; rfl

theorem projectiveChartFormPair_definite
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (n : ℕ) (a : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n)
    (ha : projectiveChartFormPair V e he y hy n a a = 0) : a = 0 := by
  apply metricCoordinateForm_injective V e he y hy n
  rw [metricCoordinateForm_zero]
  exact ExteriorPair.Constructions.formMetricPair_definite n _ ha

/-- A global pairing on the actual covector fields, computed through a chart at the point. -/
def projectiveFormPointPair (n : ℕ) (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (x : V.analyticSpace) : ℂ :=
  projectiveChartFormPair V (chartAt V.analyticModel x) (chart_mem_atlas V.analyticModel x)
    (chartAt V.analyticModel x x) ((chartAt V.analyticModel x).map_source (mem_chart_source _ x)) n
    (a.inChart (chartAt V.analyticModel x) (chartAt V.analyticModel x x))
    (b.inChart (chartAt V.analyticModel x) (chartAt V.analyticModel x x))

theorem projectiveFormPointPair_eq_chart
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (x : V.analyticSpace) (hx : x ∈ e.source)
    (n : ℕ) (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) :
    projectiveFormPointPair V n a b x =
      projectiveChartFormPair V e he (e x) (e.map_source hx) n (a.inChart e (e x)) (b.inChart e (e x)) :=
  projectiveChartFormPair_transition V (chartAt V.analyticModel x) e
    (chart_mem_atlas V.analyticModel x) he x (mem_chart_source _ x) hx n a b

theorem projectiveFormPointPair_symm (n : ℕ) (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (x : V.analyticSpace) :
    star (projectiveFormPointPair V n b a x) = projectiveFormPointPair V n a b x :=
  ExteriorPair.Constructions.formMetricPair_symm n _ _

theorem projectiveFormPointPair_nonneg (n : ℕ) (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (x : V.analyticSpace) : 0 ≤ (projectiveFormPointPair V n a a x).re :=
  ExteriorPair.Constructions.formMetricPair_nonneg n _

/-- Zero pointwise metric length implies zero in the actual tangent covector fiber. -/
theorem projectiveFormPointPair_definite (n : ℕ) (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (x : V.analyticSpace) (ha : projectiveFormPointPair V n a a x = 0) : a x = 0 := by
  let e := chartAt V.analyticModel x
  have he := chart_mem_atlas V.analyticModel x
  have hx := mem_chart_source V.analyticModel x
  have hz : a.inChart e (e x) = 0 :=
    projectiveChartFormPair_definite V e he (e x) (e.map_source hx) n _ ha
  ext v
  have h := congrArg (fun form : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n =>
    form (fun i => DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx (v i))) hz
  rw [DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at a e he x hx] at h
  change a x (fun i => (DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx).symm
    (DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx (v i))) = 0 at h
  change a x v = 0
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions
