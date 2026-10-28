import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalEnergyLocalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartForcing
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalSmoothRegularity

/-! # Global Interior Smooth -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalInteriorSmooth.CM.Construction

noncomputable section

section

/-! An actual global weak metric solution with smooth forcing satisfies
the genuine local Euclidean weak equation after chart localization. -/

open _root_.MeasureTheory Set Filter
open scoped SchwartzMap _root_.Topology

variable {ι : Type*} [Fintype ι]

def IsGlobalWeakMetricSolution (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) : Prop :=
  ∀ v : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b,
    (∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b u x))
      (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b v x) ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
      inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F) (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b v)

theorem globalWeakMetricSolution_local (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (hsol : IsGlobalWeakMetricSolution V C b u F)
    (η χ : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (hηc : HasCompactSupport (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hηU : tsupport η ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hχc : HasCompactSupport (χ : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hχU : tsupport χ ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (U : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (hU : U ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hη : ∀ z ∈ U, (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1)
    (hχ : ∀ z ∈ U, χ z = 1)
    (A : EuclideanMetric.CM.Construction.varietyEuclideanModel V → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ∀ z ∈ U, A z = MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b z)
    (hAm : AEStronglyMeasurable A volume) {B : ℝ} (hAB : ∀ᵐ z ∂volume, ‖A z‖ ≤ B) :
    LocalSmoothRegularity.CM.Construction.IsLocalEuclideanWeakMetricSolution b A U
      (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he η hηc hηU u).val
      ((‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2)⁻¹ •
        (ChartForcing.CM.Construction.varietyChartForcing V e he χ hχc hχU F).toLp 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V))) := by
  apply LocalSmoothRegularity.CM.Construction.localWeakMetricSolution_of_schwartz_tests b A hAm hAB
  intro g hgc hgU
  have hgChart := hgU.trans hU
  have hE := GlobalEnergyLocalization.CM.Construction.varietyGlobalEnergy_localization V C b e he g η hgc hgChart hηc hηU
    (fun z hz => hη z (hgU hz)) A (fun z hz => hA z (hgU hz)) hAm hAB u
  have hs := hsol (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hgChart))
  rw [GlobalSobolevGraph.CM.Construction.varietySobolevDerivative_smooth, GlobalSobolevGraph.CM.Construction.varietySobolevFunction_smooth] at hs
  have hF := ChartForcing.CM.Construction.varietyChartForcing_pairing V e he F g χ hgc hgChart hχc hχU (fun z hz => hχ z (hgU hz))
  have hκ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hq : ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hκ)
  have hEq : ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 *
      (∫ z, inner ℝ (A z (EuclideanGradient.CM.Construction.sobolevVectorGradient b
        (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he η hηc hηU u).val z))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g) z)) =
      inner ℝ ((ChartForcing.CM.Construction.varietyChartForcing V e he χ hχc hχU F).toLp 2) (g.toLp 2) :=
    hE.symm.trans (hs.trans hF)
  rw [real_inner_smul_left]
  have h := congrArg (fun x : ℝ => (‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2)⁻¹ * x) hEq
  simpa only [← mul_assoc, inv_mul_cancel₀ hq, one_mul] using h

end

/-! Actual global weak metric solutions with smooth forcing have smooth
representatives locally in every chart, by the proved elliptic bootstrap. -/

open _root_.MeasureTheory TemperedDistribution Set Filter
open scoped SchwartzMap ContDiff _root_.Topology

theorem real_smul_schwartz_memSobolev {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (r s : ℝ) (g : 𝓢(E, ℂ)) :
    MemSobolev s 2 ((r • g.toLp 2 (volume : Measure E) : Lp ℂ 2 volume) : 𝓢'(E, ℂ)) := by
  have heq : (r • g.toLp 2 (volume : Measure E) : Lp ℂ 2 volume) =
      (r : ℂ) • g.toLp 2 (volume : Measure E) :=
    (IsScalarTower.algebraMap_smul ℂ r _).symm
  rw [heq, ← Lp.toTemperedDistributionCLM_apply, map_smul,
    Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_toLp_eq]
  exact g.memSobolev.smul (r : ℂ)

theorem globalWeakMetricSolution_smooth_interior (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (hsol : IsGlobalWeakMetricSolution V C b u F)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ (η : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
      (hηc : HasCompactSupport (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
      (hηU : tsupport η ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e),
      (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1 ∧
      ∃ g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1 ∧
        ∃ v : BoundedContinuousFunction (EuclideanMetric.CM.Construction.varietyEuclideanModel V) ℂ,
          SobolevInv.CM.Construction.boundedFunctionDistribution v = (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
            (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he η hηc hηU u).val) :
              𝓢'(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) ∧
          ContDiff ℝ (⊤ : ℕ∞) (v : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) := by
  obtain ⟨η, hηc, hηU, _hηreal, hηz⟩ := NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact
    (isCompact_singleton (x := z)) (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (singleton_subset_iff.mpr hz)
  have hηz' := hηz z (mem_singleton z)
  obtain ⟨A, hAz, hAc, hA, ⟨B, hB⟩, ⟨L, hL⟩, a, ha, hpos⟩ :=
    SmoothMetricLocalization.CM.Construction.variety_exists_compact_smooth_metric_extension V e he b hz
  have hW : ({x | A x = MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b x} ∩ {x | η x = 1}) ∩
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) ∈ 𝓝 z :=
    inter_mem (inter_mem hAz hηz') ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)
  obtain ⟨U, hUW, hU, hzU⟩ := mem_nhds_iff.mp hW
  have hηlocal : ∀ x ∈ U, (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 x] 1 := by
    intro x hx
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hUW hy).1.2
  let f : Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
    (‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2)⁻¹ •
      (ChartForcing.CM.Construction.varietyChartForcing V e he η hηc hηU F).toLp 2 volume
  have hlocal : LocalSmoothRegularity.CM.Construction.IsLocalEuclideanWeakMetricSolution b A U
      (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he η hηc hηU u).val f :=
    globalWeakMetricSolution_local V C b e he u F hsol η η hηc hηU hηc hηU U
      (fun _ hx => (hUW hx).2) hηlocal (fun _ hx => (hUW hx).1.2) A
      (fun _ hx => (hUW hx).1.1) hA.continuous.aestronglyMeasurable (Eventually.of_forall hB)
  have hf : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (f : 𝓢'(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) :=
    fun n => real_smul_schwartz_memSobolev _ (n : ℝ) (ChartForcing.CM.Construction.varietyChartForcing V e he η hηc hηU F)
  exact ⟨η, hηc, hηU, hηz', LocalSmoothRegularity.CM.Construction.local_elliptic_smooth_near_point b A
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℂ ι)) hA hAc hL hB ha hpos hU _ f hlocal hf hzU⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalInteriorSmooth.CM.Construction
