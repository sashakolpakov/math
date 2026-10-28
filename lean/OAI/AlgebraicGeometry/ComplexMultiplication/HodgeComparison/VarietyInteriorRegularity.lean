import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalElliptic
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothMetricLocalization

/-! # Variety Interior Regularity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietyInteriorRegularity.CM.Construction

noncomputable section

/-! Actual interior H2 regularity of the weak Dirichlet solution for the
projective metric, without an additional coefficient hypothesis. -/

open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ContDiff _root_.Topology _root_.Manifold

theorem exists_real_schwartz_local_cutoff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {z : E} (hz : z ∈ U) :
    ∃ g : 𝓢(E, ℂ), tsupport g ⊆ U ∧
      (∀ x, g x = Complex.ofReal (g x).re) ∧ (g : E → ℂ) =ᶠ[𝓝 z] 1 := by
  obtain ⟨η, hη, hηc, hηU, _, _, hηz⟩ := SmoothMetricLocalization.CM.Construction.exists_smooth_local_cutoff hU hz
  have hηℂc : HasCompactSupport (fun x => Complex.ofReal (η x)) :=
    hηc.comp_left (show Complex.ofReal 0 = 0 from rfl)
  have hηℂ : ContDiff ℝ ∞ (fun x => Complex.ofReal (η x)) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (∞ : ℕ∞ω))
      (E := ℝ) (F := ℂ) Complex.ofRealCLM).comp hη
  let g : 𝓢(E, ℂ) := hηℂc.toSchwartzMap hηℂ
  have hs : Function.support (g : E → ℂ) ⊆ Function.support η := by
    intro x hx hzero
    apply hx
    change Complex.ofReal (η x) = 0
    rw [hzero, Complex.ofReal_zero]
  refine ⟨g, (closure_mono hs).trans hηU, ?_, ?_⟩
  · intro x
    change Complex.ofReal (η x) = Complex.ofReal (Complex.ofReal (η x)).re
    rw [Complex.ofReal_re]
  · filter_upwards [hηz] with x hx
    change Complex.ofReal (η x) = 1
    rw [show η x = 1 from hx, Complex.ofReal_one]

variable {ι : Type*} [Fintype ι]

theorem variety_metric_weak_solution_interior_h2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (u : SobolevIs.CM.Construction.supportedH1Coordinates K) (f : Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hsol : ∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
      (∫ x, inner ℝ (MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K x (GradientSupport.CM.Construction.supportedH1VectorGradient b K u x))
        (GradientSupport.CM.Construction.supportedH1VectorGradient b K v x)) = inner ℝ f (SobolevIs.CM.Construction.supportedH1Embedding K v))
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ interior K) :
    ∃ g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ),
      (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1 ∧
      MemSobolev 2 2 ((SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
        (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u.val) : Lp ℂ 2 volume) : 𝓢'(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) := by
  obtain ⟨A, hAz, _, ⟨C, hC⟩, ⟨L, hL⟩, a, ha, hpos⟩ :=
    SmoothMetricLocalization.CM.Construction.variety_exists_smooth_metric_extension V e he b (hKU (interior_subset hz))
  have hW : {x | A x = MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b x} ∩ interior K ∈ 𝓝 z :=
    Filter.inter_mem hAz (isOpen_interior.mem_nhds hz)
  obtain ⟨U, hUW, hU, hzU⟩ := mem_nhds_iff.mp hW
  obtain ⟨g, hgU, hgreal, hgz⟩ := exists_real_schwartz_local_cutoff hU hzU
  have hgK : Function.support (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) ⊆ K :=
    (subset_tsupport g).trans (hgU.trans (hUW.trans (inter_subset_right.trans interior_subset)))
  have hAB : ∀ x ∈ tsupport g, A x = MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K x := by
    intro x hx
    have hw := hUW (hgU hx)
    rw [hw.1, MetricDirichlet.CM.Construction.varietyMetricDirichletOperator,
      EllipticExtension.CM.Construction.ellipticFieldExtension_of_mem K _ (interior_subset hw.2)]
  refine ⟨g, hgz, ?_⟩
  exact LocalElliptic.CM.Construction.supported_weak_solution_interior_h2 b A (MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K)
    hL hC ha hpos g hgreal hgK hAB u f hsol

/-- The actual metric Dirichlet equation has a weak solution which is H2
near every interior point of the chosen compact coordinate domain. -/
theorem variety_metric_dirichlet_exists_interior_h2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [Nontrivial (EuclideanMetric.CM.Construction.varietyEuclideanModel V)]
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    ∃ u : SobolevIs.CM.Construction.supportedH1Coordinates K,
      (∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
        (∫ x, inner ℝ (MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K x (GradientSupport.CM.Construction.supportedH1VectorGradient b K u x))
          (GradientSupport.CM.Construction.supportedH1VectorGradient b K v x)) = inner ℝ f (SobolevIs.CM.Construction.supportedH1Embedding K v)) ∧
      ∀ z ∈ interior K, ∃ g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ),
        (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1 ∧
        MemSobolev 2 2 ((SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
          (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u.val) : Lp ℂ 2 volume) : 𝓢'(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) := by
  let ℓ := (innerSL ℝ f).comp ((SobolevIs.CM.Construction.supportedH1Embedding K).restrictScalars ℝ)
  obtain ⟨u, hu, _⟩ := MetricDirichlet.CM.Construction.variety_metric_dirichlet_weak_existsUnique V e he b hK hKU ℓ
  refine ⟨u, hu, fun z hz => ?_⟩
  exact variety_metric_weak_solution_interior_h2 V e he b hKU u f hu hz

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietyInteriorRegularity.CM.Construction
