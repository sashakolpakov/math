import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartLpPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ScalarChartLocalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential

/-! # Chart Cutoff Lp -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartCutoffLp.CM.Construction

noncomputable section

/-! Smooth compact chart cutoffs act boundedly on the actual global L2
space and coincide with the localized Schwartz functions on smooth inputs. -/

open _root_.MeasureTheory Set Filter
open scoped SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def varietyChartCutoffL2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Lp F 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ] Lp F 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  ((CutoffDifferential.CM.Construction.schwartzL2Multiply g).restrictScalars ℝ).comp (ChartLpPullback.CM.Construction.varietyChartL2Localization V e he hgc hg)

theorem varietyChartCutoffL2_coe_of_ae (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (u : Lp F 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) (f : V.analyticSpace → F)
    (hf : u =ᵐ[GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V] f) :
    varietyChartCutoffL2 V e he g hgc hg u =ᵐ[volume]
      fun z => g z • f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
  filter_upwards [CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g (ChartLpPullback.CM.Construction.varietyChartL2Localization V e he hgc hg u),
    ChartLpPullback.CM.Construction.varietyChartL2Localization_coe_of_ae V e he hgc hg u f hf] with z hmul hloc
  change CutoffDifferential.CM.Construction.schwartzL2Multiply g (ChartLpPullback.CM.Construction.varietyChartL2Localization V e he hgc hg u) z = _
  rw [hmul, hloc]
  by_cases hz : z ∈ tsupport g
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz, zero_smul, zero_smul]

theorem varietyChartCutoffL2_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    varietyChartCutoffL2 V e he g hgc hg (GlobalLp.CM.Construction.varietySmoothScalarL2 V f) =
      (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f).toLp 2 volume := by
  apply Lp.ext
  refine (varietyChartCutoffL2_coe_of_ae V e he g hgc hg (GlobalLp.CM.Construction.varietySmoothScalarL2 V f)
    (HolomorphicPrimitive.CM.Construction.zeroFormScalar f) (GlobalLp.CM.Construction.varietySmoothScalarL2_coe V f)).trans ?_
  exact ((ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f).coeFn_toLp 2 volume).symm

def varietyScalarChartCutoffLinear (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ] 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ) where
  toFun := ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg
  map_add' f h := by
    ext z
    change g z * (HolomorphicPrimitive.CM.Construction.zeroFormScalar f _ + HolomorphicPrimitive.CM.Construction.zeroFormScalar h _) =
      g z * HolomorphicPrimitive.CM.Construction.zeroFormScalar f _ + g z * HolomorphicPrimitive.CM.Construction.zeroFormScalar h _
    exact mul_add _ _ _
  map_smul' a f := by
    ext z
    change g z * (a * HolomorphicPrimitive.CM.Construction.zeroFormScalar f _) = a * (g z * HolomorphicPrimitive.CM.Construction.zeroFormScalar f _)
    ring

def varietyScalarChartSobolevCoordinate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1).comp (varietyScalarChartCutoffLinear V e he g hgc hg)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartCutoffLp.CM.Construction
