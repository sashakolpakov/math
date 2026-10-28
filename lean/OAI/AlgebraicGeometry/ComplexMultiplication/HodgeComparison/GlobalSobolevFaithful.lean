import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalizedDifferential
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormLocalizationFaithful

/-! # Global Sobolev Faithful -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSobolevFaithful.CM.Construction

noncomputable section

/-! The completion of the actual derivative graph is a genuine space of
L2 functions: its function projection is injective. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap

theorem varietySobolevFunction_eq_zero_imp (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) (hu : GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u = 0) : u = 0 := by
  have hlocal (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
      (he : e ∈ atlas V.analyticModel V.analyticSpace)
      (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
      (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
      OneFormChartLocalization.CM.Construction.varietyOneFormChartL2 V C b e he g hgc hg (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b u) = 0 := by
    have hS : GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he g hgc hg u = 0 := by
      apply SobolevIs.CM.Construction.supportedH1Embedding_injective (tsupport g)
      rw [GlobalLocalization.CM.Construction.varietySobolevChartLocalization_function, hu, map_zero, map_zero]
    have hSval : (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he g hgc hg u).val = 0 :=
      congrArg Subtype.val hS
    apply LpComponents.CM.Construction.complexLpComponent_eq_zero (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    intro i
    have h := LocalizedDifferential.CM.Construction.varietyLocalizedDifferential V C b e he g hgc hg u i
    rw [hSval, hu, map_zero, map_zero, zero_add] at h
    exact h.symm
  let G := FiniteMetricCutoffs.CM.Construction.projectiveMetricCutoffs V C
  have hD : GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b u = 0 :=
    OneFormLocalizationFaithful.CM.Construction.varietyOneFormChartL2_detects_zero V C G b _ (fun i =>
      hlocal (C.chart i) (C.chart_mem i) (G.cutoff i) (G.compact_support i) (G.supported i))
  have hnorm := GlobalSobolevGraph.CM.Construction.varietySobolevGraph_norm_sq V C b u
  simp only [hu, hD, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hnorm
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

theorem varietySobolevFunction_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    Function.Injective (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply varietySobolevFunction_eq_zero_imp V C b
  rw [map_sub, huv, sub_self]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSobolevFaithful.CM.Construction
