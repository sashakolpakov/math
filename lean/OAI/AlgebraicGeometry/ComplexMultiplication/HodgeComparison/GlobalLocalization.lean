import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartEstimate
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Global Localization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLocalization.CM.Construction

noncomputable section

/-! Bounded chart localization of the completed global derivative graph
into genuine supported H1 spaces. Its L2 component is the actual cutoff
pullback, so every such localized inclusion is compact. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap

def varietyScalarChartSupportedCoordinate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ] SobolevIs.CM.Construction.supportedH1Coordinates (tsupport g) :=
  (ChartCutoffLp.CM.Construction.varietyScalarChartSobolevCoordinate V e he g hgc hg).codRestrict (SobolevIs.CM.Construction.supportedH1Coordinates (tsupport g))
    (fun f => ((SobolevIs.CM.Construction.supportedSchwartzSubmodule (tsupport g)).map (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1)).le_topologicalClosure
      ⟨ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f,
        ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff_support V e he g hgc hg f, rfl⟩)

def varietySobolevChartLocalization (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b →L[ℂ] SobolevIs.CM.Construction.supportedH1Coordinates (tsupport g) :=
  (varietyScalarChartSupportedCoordinate V e he g hgc hg).extendOfNorm (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b)

theorem varietySobolevChartLocalization_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    varietySobolevChartLocalization V C b e he g hgc hg (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f) =
      varietyScalarChartSupportedCoordinate V e he g hgc hg f :=
  LinearMap.extendOfNorm_eq (f := varietyScalarChartSupportedCoordinate V e he g hgc hg)
    (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev_dense V C b)
    (ChartEstimate.CM.Construction.varietyScalarChartSobolevCoordinate_graph_bound V C b e he g hgc hg) f

theorem varietySobolevChartLocalization_function (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) :
    SobolevIs.CM.Construction.supportedH1Embedding (tsupport g) (varietySobolevChartLocalization V C b e he g hgc hg u) =
      ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he g hgc hg (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u) := by
  have h := (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev_dense V C b).equalizer
    ((SobolevIs.CM.Construction.supportedH1Embedding (tsupport g)).continuous.comp
      (varietySobolevChartLocalization V C b e he g hgc hg).continuous)
    ((ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he g hgc hg).continuous.comp (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b).continuous)
    (by
      funext f
      dsimp only [Function.comp_apply]
      rw [varietySobolevChartLocalization_smooth, GlobalSobolevGraph.CM.Construction.varietySobolevFunction_smooth]
      change SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
        (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f)) = _
      rw [SobolevIs.CM.Construction.sobolevL2Embedding_schwartz, ChartCutoffLp.CM.Construction.varietyChartCutoffL2_smooth])
  exact congrFun h u

theorem varietySobolevChartCutoff_isCompact (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    IsCompactOperator ((ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he g hgc hg).comp
      ((GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b).restrictScalars ℝ)) := by
  have h := (SobolevIs.CM.Construction.supportedH1Embedding_isCompact hgc).comp_clm (varietySobolevChartLocalization V C b e he g hgc hg)
  have heq : (fun u => ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he g hgc hg (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u)) =
      (SobolevIs.CM.Construction.supportedH1Embedding (tsupport g)).comp (varietySobolevChartLocalization V C b e he g hgc hg) :=
    funext (fun u => (varietySobolevChartLocalization_function V C b e he g hgc hg u).symm)
  change IsCompactOperator (fun u => ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he g hgc hg (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u))
  rw [heq]
  exact h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLocalization.CM.Construction
