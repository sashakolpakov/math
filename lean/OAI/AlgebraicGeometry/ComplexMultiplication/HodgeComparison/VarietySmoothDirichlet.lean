import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalSmoothRegularity

/-! # Variety Smooth Dirichlet -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietySmoothDirichlet.CM.Construction

noncomputable section

/-! The actual projective metric Dirichlet solver has genuine smooth interior
representatives for smooth Sobolev forcing, in particular Schwartz forcing. -/

open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ContDiff _root_.Topology _root_.Manifold

variable {ι : Type*} [Fintype ι]

theorem variety_metric_weak_solution_smooth_interior (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (u : SobolevIs.CM.Construction.supportedH1Coordinates K) (f : Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hsol : ∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
      (∫ x, inner ℝ (MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K x (GradientSupport.CM.Construction.supportedH1VectorGradient b K u x))
        (GradientSupport.CM.Construction.supportedH1VectorGradient b K v x)) = inner ℝ f (SobolevIs.CM.Construction.supportedH1Embedding K v))
    (hf : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (f : 𝓢'(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)))
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ interior K) :
    ∃ g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1 ∧
      ∃ v : BoundedContinuousFunction (EuclideanMetric.CM.Construction.varietyEuclideanModel V) ℂ,
        SobolevInv.CM.Construction.boundedFunctionDistribution v = (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
          (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u.val) : 𝓢'(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) ∧
        ContDiff ℝ (⊤ : ℕ∞) (v : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) := by
  obtain ⟨A, hAz, hAc, hA, ⟨C, hC⟩, ⟨L, hL⟩, a, ha, hpos⟩ :=
    SmoothMetricLocalization.CM.Construction.variety_exists_compact_smooth_metric_extension V e he b (hKU (interior_subset hz))
  have hW : {x | A x = MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b x} ∩ interior K ∈ 𝓝 z :=
    Filter.inter_mem hAz (isOpen_interior.mem_nhds hz)
  obtain ⟨U, hUW, hU, hzU⟩ := mem_nhds_iff.mp hW
  have hlocal : LocalSmoothRegularity.CM.Construction.IsLocalEuclideanWeakMetricSolution b A U u.val f := by
    intro g _hgc _hgreal hgU v
    have hgK : Function.support (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) ⊆ K :=
      (subset_tsupport g).trans (hgU.trans (hUW.trans (inter_subset_right.trans interior_subset)))
    have hAB : ∀ x ∈ tsupport g, A x = MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K x := by
      intro x hx
      have hw := hUW (hgU hx)
      rw [hw.1, MetricDirichlet.CM.Construction.varietyMetricDirichletOperator,
        EllipticExtension.CM.Construction.ellipticFieldExtension_of_mem K _ (interior_subset hw.2)]
    rw [LocalElliptic.CM.Construction.cutoff_energy_coefficient_eq b A (MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K) g hAB]
    exact hsol ⟨SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v, SobolevSmoothDensity.CM.Construction.sobolevCutoffCLM_mem_supported g hgK v⟩
  exact LocalSmoothRegularity.CM.Construction.local_elliptic_smooth_near_point b A (ContinuousLinearMap.id ℝ (EuclideanSpace ℂ ι))
    hA hAc hL hC ha hpos hU u.val f hlocal hf hzU

theorem variety_metric_dirichlet_exists_smooth_interior (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [Nontrivial (EuclideanMetric.CM.Construction.varietyEuclideanModel V)]
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hf : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (f : 𝓢'(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))) :
    ∃ u : SobolevIs.CM.Construction.supportedH1Coordinates K,
      (∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
        (∫ x, inner ℝ (MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K x (GradientSupport.CM.Construction.supportedH1VectorGradient b K u x))
          (GradientSupport.CM.Construction.supportedH1VectorGradient b K v x)) = inner ℝ f (SobolevIs.CM.Construction.supportedH1Embedding K v)) ∧
      ∀ z ∈ interior K, ∃ g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ),
        (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1 ∧
        ∃ v : BoundedContinuousFunction (EuclideanMetric.CM.Construction.varietyEuclideanModel V) ℂ,
          SobolevInv.CM.Construction.boundedFunctionDistribution v = (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
            (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u.val) : 𝓢'(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) ∧
          ContDiff ℝ (⊤ : ℕ∞) (v : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) := by
  let ℓ := (innerSL ℝ f).comp ((SobolevIs.CM.Construction.supportedH1Embedding K).restrictScalars ℝ)
  obtain ⟨u, hu, _⟩ := MetricDirichlet.CM.Construction.variety_metric_dirichlet_weak_existsUnique V e he b hK hKU ℓ
  exact ⟨u, hu, fun _ hz => variety_metric_weak_solution_smooth_interior V e he b hKU u f hu hf hz⟩

/-- Smooth rapidly decreasing forcing gives a genuine weak projective-metric
Dirichlet solution which is smooth near every interior point. -/
theorem variety_metric_dirichlet_schwartz_exists_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [Nontrivial (EuclideanMetric.CM.Construction.varietyEuclideanModel V)]
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) :
    ∃ u : SobolevIs.CM.Construction.supportedH1Coordinates K,
      (∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
        (∫ x, inner ℝ (MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K x (GradientSupport.CM.Construction.supportedH1VectorGradient b K u x))
          (GradientSupport.CM.Construction.supportedH1VectorGradient b K v x)) = inner ℝ (f.toLp 2 volume) (SobolevIs.CM.Construction.supportedH1Embedding K v)) ∧
      ∀ z ∈ interior K, ∃ g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ),
        (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1 ∧
        ∃ v : BoundedContinuousFunction (EuclideanMetric.CM.Construction.varietyEuclideanModel V) ℂ,
          SobolevInv.CM.Construction.boundedFunctionDistribution v = (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
            (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u.val) : 𝓢'(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) ∧
          ContDiff ℝ (⊤ : ℕ∞) (v : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) := by
  apply variety_metric_dirichlet_exists_smooth_interior V e he b hK hKU (f.toLp 2 volume)
  intro n
  rw [Lp.toTemperedDistribution_toLp_eq]
  exact f.memSobolev

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietySmoothDirichlet.CM.Construction
