import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalInteriorSmooth
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth

/-! # Global Local Representative -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLocalRepresentative.CM.Construction

noncomputable section

/-! The local smooth solution represents the actual global L2 function
almost everywhere on a neighborhood in chart coordinates. -/

open _root_.MeasureTheory Set Filter
open scoped SchwartzMap ContDiff _root_.Topology

theorem globalWeakMetricSolution_local_representative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (hsol : GlobalInteriorSmooth.CM.Construction.IsGlobalWeakMetricSolution V C b u F)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ U : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V), IsOpen U ∧ z ∈ U ∧ U ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      ∃ v : BoundedContinuousFunction (EuclideanMetric.CM.Construction.varietyEuclideanModel V) ℂ,
        ContDiff ℝ (⊤ : ℕ∞) (v : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) ∧
        ∀ᵐ y ∂(volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)), y ∈ U →
          v y = GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y)) := by
  obtain ⟨η, hηc, hηU, hηz, g, hgz, v, hv, hvs⟩ :=
    GlobalInteriorSmooth.CM.Construction.globalWeakMetricSolution_smooth_interior V C b e he u F hsol hz
  have hJ : SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
      (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he η hηc hηU u).val =
      ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he η hηc hηU (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u) :=
    GlobalLocalization.CM.Construction.varietySobolevChartLocalization_function V C b e he η hηc hηU u
  rw [CutoffDifferential.CM.Construction.sobolevCutoffCLM_embedding, hJ] at hv
  have hvae := Smooth.CM.Construction.boundedFunctionDistribution_eq_lp_ae v _ hv
  have hcut := ChartCutoffLp.CM.Construction.varietyChartCutoffL2_coe_of_ae V e he η hηc hηU
    (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u) (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u) Filter.EventuallyEq.rfl
  have hmul := CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g (ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he η hηc hηU (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u))
  have hW : ({y | η y = 1} ∩ {y | g y = 1}) ∩
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) ∈ 𝓝 z :=
    inter_mem (inter_mem hηz hgz) ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)
  obtain ⟨U, hUW, hU, hzU⟩ := mem_nhds_iff.mp hW
  refine ⟨U, hU, hzU, fun _ hy => (hUW hy).2, v, hvs, ?_⟩
  filter_upwards [hvae, hcut, hmul] with y hy hc hm
  intro hyU
  rw [hy, hm, hc, (hUW hyU).1.1, (hUW hyU).1.2, one_smul, one_smul]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLocalRepresentative.CM.Construction
