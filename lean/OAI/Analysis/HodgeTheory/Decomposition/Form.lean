import OAI.Analysis.HodgeTheory.Decomposition.PositiveVolume
import OAI.Analysis.HodgeTheory.Decomposition.GlobalOrthogonality
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.InnerProductSpace.Completion

/-! # Form -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Form.Constructions

noncomputable section

/-! The genuine L² Hermitian pairing on smooth differential forms, using the
constructed projective metric and its finite full-support volume. -/

open scoped _root_.Manifold
open _root_.MeasureTheory

section FiberAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem formMetricPair_add_left (n : ℕ) (a b c : DifferentialForms.Manifold.Basic.FormValue E n) :
    ExteriorPair.Constructions.formMetricPair n (a + b) c = ExteriorPair.Constructions.formMetricPair n a c + ExteriorPair.Constructions.formMetricPair n b c := by
  unfold ExteriorPair.Constructions.formMetricPair CovectorPair.Constructions.covectorInner
  rw [map_add, CovectorPair.Constructions.covectorBasisPair_add_left]

theorem formMetricPair_self_re (n : ℕ) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    ((ExteriorPair.Constructions.formMetricPair n a a).re : ℂ) = ExteriorPair.Constructions.formMetricPair n a a := by
  unfold ExteriorPair.Constructions.formMetricPair CovectorPair.Constructions.covectorInner
  rw [CovectorPair.Constructions.covectorBasisPair_self]
  rfl

end FiberAlgebra

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)

theorem projectiveChartFormPair_add_left
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (y : V.analyticModel) (hy : y ∈ e.target)
    (a b c : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n) :
    ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n (a + b) c =
      ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a c + ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n b c := by
  unfold ProjectiveFormMetric.Constructions.projectiveChartFormPair
  have hab : ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n (a + b) =
      ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n a + ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n b := by ext v; rfl
  rw [hab, formMetricPair_add_left]

theorem projectiveChartFormPair_smul_left
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (y : V.analyticModel) (hy : y ∈ e.target)
    (a b : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n) (z : ℂ) :
    ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n (z • a) b =
      star z * ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a b := by
  unfold ProjectiveFormMetric.Constructions.projectiveChartFormPair
  have hza : ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n (z • a) =
      z • ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n a := by ext v; rfl
  rw [hza, UnitaryTypes.Constructions.formMetricPair_smul_left]

theorem projectiveFormPointPair_add_left (a b c : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (x : V.analyticSpace) :
    ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (a + b) c x =
      ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a c x + ProjectiveFormMetric.Constructions.projectiveFormPointPair V n b c x := by
  unfold ProjectiveFormMetric.Constructions.projectiveFormPointPair
  rw [DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Pi.add_apply, projectiveChartFormPair_add_left]

theorem projectiveFormPointPair_smul_left (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (z : ℂ) (x : V.analyticSpace) :
    ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (z • a) b x = star z * ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b x := by
  unfold ProjectiveFormMetric.Constructions.projectiveFormPointPair
  rw [DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, Pi.smul_apply, projectiveChartFormPair_smul_left]

theorem projectiveFormPointPair_self_re (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (x : V.analyticSpace) :
    ((ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a a x).re : ℂ) = ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a a x :=
  formMetricPair_self_re n _

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveFormPointPair_integrable
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    Integrable (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val b.val) (MeasureVolume.Constructions.projectiveMetricVolume V) :=
  (MetricCoefficients.Constructions.projectiveFormPointPair_continuous V n a b).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The L² pairing is the integral of the genuine pointwise metric against its own volume. -/
def projectiveL2Pair (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) : ℂ :=
  ∫ x, ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val b.val x ∂ MeasureVolume.Constructions.projectiveMetricVolume V

omit [BorelSpace V.analyticSpace] in
theorem projectiveL2Pair_symm (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    star (projectiveL2Pair V n b a) = projectiveL2Pair V n a b := by
  unfold projectiveL2Pair
  change (starRingEnd ℂ) (∫ x, ProjectiveFormMetric.Constructions.projectiveFormPointPair V n b.val a.val x ∂ MeasureVolume.Constructions.projectiveMetricVolume V) = _
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm V n a.val b.val x)

theorem projectiveL2Pair_add_left (a b c : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    projectiveL2Pair V n (a + b) c = projectiveL2Pair V n a c + projectiveL2Pair V n b c := by
  unfold projectiveL2Pair
  change (∫ x, ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (a.val + b.val) c.val x ∂ MeasureVolume.Constructions.projectiveMetricVolume V) = _
  simp_rw [projectiveFormPointPair_add_left]
  exact integral_add (projectiveFormPointPair_integrable V n a c) (projectiveFormPointPair_integrable V n b c)

omit [BorelSpace V.analyticSpace] in
theorem projectiveL2Pair_smul_left (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (z : ℂ) :
    projectiveL2Pair V n (z • a) b = star z * projectiveL2Pair V n a b := by
  unfold projectiveL2Pair
  change (∫ x, ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (z • a.val) b.val x ∂ MeasureVolume.Constructions.projectiveMetricVolume V) = _
  simp_rw [projectiveFormPointPair_smul_left]
  exact integral_const_mul _ _

theorem projectiveL2Pair_nonneg (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    0 ≤ (projectiveL2Pair V n a a).re := by
  change 0 ≤ RCLike.re (∫ x, ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x ∂ MeasureVolume.Constructions.projectiveMetricVolume V)
  rw [← integral_re (projectiveFormPointPair_integrable V n a a)]
  exact integral_nonneg (fun x => ProjectiveFormMetric.Constructions.projectiveFormPointPair_nonneg V n a.val x)

/-- Vanishing of the L² norm forces the actual smooth differential form to vanish. -/
theorem projectiveL2Pair_definite (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (ha : projectiveL2Pair V n a a = 0) : a = 0 := by
  have hInt := projectiveFormPointPair_integrable V n a a
  have hrealInt : (∫ x, (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re ∂ MeasureVolume.Constructions.projectiveMetricVolume V) = 0 := by
    have h := integral_re hInt
    change (∫ x, (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re ∂ MeasureVolume.Constructions.projectiveMetricVolume V) =
      (projectiveL2Pair V n a a).re at h
    rw [ha, Complex.zero_re] at h
    exact h
  have hReInt : Integrable (fun x => (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re)
      (MeasureVolume.Constructions.projectiveMetricVolume V) := Complex.reCLM.integrable_comp hInt
  have hAE := (integral_eq_zero_iff_of_nonneg
    (fun x => ProjectiveFormMetric.Constructions.projectiveFormPointPair_nonneg V n a.val x) hReInt).mp hrealInt
  have hAll := Measure.eq_of_ae_eq hAE
    (Complex.continuous_re.comp (MetricCoefficients.Constructions.projectiveFormPointPair_continuous V n a a)) continuous_const
  apply DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  apply ProjectiveFormMetric.Constructions.projectiveFormPointPair_definite V n a.val x
  have hx : (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re = 0 := congrFun hAll x
  rw [← projectiveFormPointPair_self_re, hx, Complex.ofReal_zero]

/-- Positive Hermitian data for the actual smooth-form L² norm. -/
@[instance_reducible] def projectiveL2Core :
    InnerProductSpace.Core ℂ (DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) where
  inner := projectiveL2Pair V n
  conj_inner_symm a b := by
    change star (projectiveL2Pair V n b a) = _
    exact projectiveL2Pair_symm V n a b
  add_left := projectiveL2Pair_add_left V n
  smul_left := fun a b z => projectiveL2Pair_smul_left V n a b z
  re_inner_nonneg := projectiveL2Pair_nonneg V n
  definite := projectiveL2Pair_definite V n

/-- Smooth forms with their genuine L² norm, kept on a distinct normed type. -/
abbrev ProjectivePreL2Forms :=
  MetricFiber.Constructions.HermitianFiber (DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (projectiveL2Core V n)

/-- The Hilbert completion of the actual smooth differential forms in the metric L² norm. -/
abbrev ProjectiveL2Forms := UniformSpace.Completion (ProjectivePreL2Forms V n)

/-- The actual smooth forms embed linearly in their metric Hilbert completion. -/
def smoothToProjectiveL2 :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ] ProjectiveL2Forms V n :=
  (UniformSpace.Completion.toComplₗᵢ : ProjectivePreL2Forms V n →ₗᵢ[ℂ] ProjectiveL2Forms V n).toLinearMap.comp
    (MetricFiber.Constructions.hermitianFiberEquiv _ (projectiveL2Core V n)).symm.toLinearMap

theorem smoothToProjectiveL2_injective : Function.Injective (smoothToProjectiveL2 V n) :=
  (UniformSpace.Completion.toComplₗᵢ : ProjectivePreL2Forms V n →ₗᵢ[ℂ] ProjectiveL2Forms V n).injective.comp
    (MetricFiber.Constructions.hermitianFiberEquiv _ (projectiveL2Core V n)).symm.injective

/-- The completion's Hilbert inner product agrees with the actual integral on smooth forms. -/
theorem smoothToProjectiveL2_inner (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    inner ℂ (smoothToProjectiveL2 V n a) (smoothToProjectiveL2 V n b) = projectiveL2Pair V n a b := by
  change inner ℂ (((MetricFiber.Constructions.hermitianFiberEquiv _ (projectiveL2Core V n)).symm a : ProjectivePreL2Forms V n) : ProjectiveL2Forms V n)
    (((MetricFiber.Constructions.hermitianFiberEquiv _ (projectiveL2Core V n)).symm b : ProjectivePreL2Forms V n) : ProjectiveL2Forms V n) = _
  rw [UniformSpace.Completion.inner_coe]
  rfl

/-- Smooth forms are dense in the constructed metric Hilbert space. -/
theorem smoothToProjectiveL2_dense : DenseRange (smoothToProjectiveL2 V n) := by
  have hr : Set.range (smoothToProjectiveL2 V n) =
      Set.range ((↑) : ProjectivePreL2Forms V n → ProjectiveL2Forms V n) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(MetricFiber.Constructions.hermitianFiberEquiv _ (projectiveL2Core V n)).symm a, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨MetricFiber.Constructions.hermitianFiberEquiv _ (projectiveL2Core V n) a, ?_⟩
      change (((MetricFiber.Constructions.hermitianFiberEquiv _ (projectiveL2Core V n)).symm
        (MetricFiber.Constructions.hermitianFiberEquiv _ (projectiveL2Core V n) a) : ProjectivePreL2Forms V n) : ProjectiveL2Forms V n) = _
      rw [LinearEquiv.symm_apply_apply]
  change Dense (Set.range (smoothToProjectiveL2 V n))
  rw [hr]
  exact UniformSpace.Completion.denseRange_coe

end

end OAI.Analysis.HodgeTheory.Decomposition.Form.Constructions
