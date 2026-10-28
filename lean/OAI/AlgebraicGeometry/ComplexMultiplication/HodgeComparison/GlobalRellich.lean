import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartLpPushforward
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FiniteMetricCutoffs
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLocalization

/-! # Global Rellich -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalRellich.CM.Construction

noncomputable section

/-! The genuine global metric L2 inclusion is compact: finitely many
compact chart inclusions reconstruct it through bounded maps. -/

open _root_.MeasureTheory Set Filter

def varietyL2PieceProjection (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (i : Fin C.size) : Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ] Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  (((LpLocalization.CM.Construction.lpSubtypeZeroExtension (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) (C.piece_measurable i)).toContinuousLinearMap).comp
    (LpLocalization.CM.Construction.lpSubtypeRestriction (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) (C.piece_measurable i))).restrictScalars ℝ

def varietyL2PieceReconstruction (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (G : FiniteMetricCutoffs.CM.Construction.CompactMetricCutoffs V C) (i : Fin C.size) :
    Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) →L[ℝ] Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  (varietyL2PieceProjection V C i).comp
    (ChartLpPushforward.CM.Construction.varietyChartL2Pushforward V (C.chart i) (C.chart_mem i) (G.compact_support i) (G.supported i))

theorem varietyL2PieceReconstruction_cutoff_coe (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (G : FiniteMetricCutoffs.CM.Construction.CompactMetricCutoffs V C) (i : Fin C.size)
    (u : Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) :
    varietyL2PieceReconstruction V C G i
      (ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V (C.chart i) (C.chart_mem i) (G.cutoff i) (G.compact_support i) (G.supported i) u) =ᵐ[
        GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V] (C.piece i).indicator u := by
  let e := C.chart i
  let g := G.cutoff i
  let v := ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e (C.chart_mem i) g (G.compact_support i) (G.supported i) u
  let w := ChartLpPushforward.CM.Construction.varietyChartL2Pushforward V e (C.chart_mem i) (G.compact_support i) (G.supported i) v
  have hv : v =ᵐ[volume] (fun z => g z • u (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) :=
    ChartCutoffLp.CM.Construction.varietyChartCutoffL2_coe_of_ae V e (C.chart_mem i) g (G.compact_support i) (G.supported i) u u Filter.EventuallyEq.rfl
  have hw := ChartLpPushforward.CM.Construction.varietyChartL2Pushforward_coe_of_ae V e (C.chart_mem i)
    (G.compact_support i) (G.supported i) v _ hv
  filter_upwards [LpLocalization.CM.Construction.lpSubtype_localization_coeFn (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) (C.piece_measurable i) w, hw] with x hpiece hwx
  change varietyL2PieceProjection V C i w x = (C.piece i).indicator u x
  rw [show varietyL2PieceProjection V C i w x = (C.piece i).indicator w x from hpiece]
  by_cases hx : x ∈ C.piece i
  · rw [indicator_of_mem hx, indicator_of_mem hx, hwx]
    have hex : x ∈ e.source := C.piece_subset_source i hx
    have hg1 : g ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) = 1 := G.one_on_compact i x (C.piece_subset i hx)
    have hzg : (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x) ∈ tsupport g := by
      apply subset_tsupport g
      change g ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ≠ 0
      rw [hg1]
      exact one_ne_zero
    have hxIm : x ∈ ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g) :=
      ⟨(EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x), hzg, by
        dsimp only
        rw [ContinuousLinearEquiv.apply_symm_apply, e.left_inv hex]⟩
    rw [indicator_of_mem hxIm]
    rw [hg1, one_smul, ContinuousLinearEquiv.apply_symm_apply, e.left_inv hex]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

theorem varietyL2_finite_reconstruction (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (G : FiniteMetricCutoffs.CM.Construction.CompactMetricCutoffs V C)
    (u : Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) :
    (∑ i, varietyL2PieceReconstruction V C G i
      (ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V (C.chart i) (C.chart_mem i) (G.cutoff i) (G.compact_support i) (G.supported i) u)) = u := by
  classical
  apply Lp.ext
  have hall : ∀ᵐ x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V, ∀ i,
      varietyL2PieceReconstruction V C G i
        (ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V (C.chart i) (C.chart_mem i) (G.cutoff i) (G.compact_support i) (G.supported i) u) x =
          (C.piece i).indicator u x :=
    ae_all_iff.mpr (fun i => varietyL2PieceReconstruction_cutoff_coe V C G i u)
  filter_upwards [hall, LpComponents.CM.Construction.lp_coe_finsetSum (fun i => varietyL2PieceReconstruction V C G i
    (ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V (C.chart i) (C.chart_mem i) (G.cutoff i) (G.compact_support i) (G.supported i) u)) Finset.univ]
    with x hx hsum
  rw [hsum]
  simp only [hx]
  obtain ⟨i, hi⟩ := C.exists_piece x
  exact C.patchField_eq (fun _ => u) hi

theorem varietySobolevFunction_isCompact (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    IsCompactOperator (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b) := by
  classical
  let G := FiniteMetricCutoffs.CM.Construction.projectiveMetricCutoffs V C
  let J := (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b).restrictScalars ℝ
  let T (i : Fin C.size) : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b →L[ℝ] Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
    (varietyL2PieceReconstruction V C G i).comp
      ((ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V (C.chart i) (C.chart_mem i) (G.cutoff i) (G.compact_support i) (G.supported i)).comp J)
  have hT (i : Fin C.size) : IsCompactOperator (T i) :=
    (GlobalLocalization.CM.Construction.varietySobolevChartCutoff_isCompact V C b (C.chart i) (C.chart_mem i)
      (G.cutoff i) (G.compact_support i) (G.supported i)).clm_comp (varietyL2PieceReconstruction V C G i)
  have hsum : IsCompactOperator (∑ i, T i : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b →L[ℝ] Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) :=
    (compactOperator (RingHom.id ℝ) (GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) (Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V))).sum_mem
      (fun i _ => hT i)
  have heq : (∑ i, T i) = J := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [sum_apply, T, ContinuousLinearMap.comp_apply]
    exact varietyL2_finite_reconstruction V C G (J u)
  rw [heq] at hsum
  exact hsum

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalRellich.CM.Construction
