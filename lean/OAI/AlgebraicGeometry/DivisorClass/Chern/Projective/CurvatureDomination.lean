import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.MetricDomination
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactChartCover

/-! # Curvature Domination -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CurvatureDomination

noncomputable section

/-! The actual projective Fubini--Study form dominates every smooth two-form after an integral multiple. -/

open Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : FiniteDimensional ℝ V.analyticModel :=
  FiniteDimensional.trans ℝ ℂ V.analyticModel

theorem smoothForm_metricInChart_continuous (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    ContinuousOn (fun x => ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm (F.val.inChart e (e x))) e.source := by
  have hF : ContDiffOn ℝ ∞ (F.val.inChart e) e.target := by
    simpa only [Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, Set.preimage_univ, Set.inter_univ] using F.smooth e he
  exact ((ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm_smooth (E := V.analyticModel)).comp_contDiffOn hF).continuousOn.comp
    e.continuousOn (fun _ hx => e.map_source hx)

theorem smoothForm_compactChart_positive_after_nat_multiple (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m → ∀ x ∈ K, ∀ v : V.analyticModel, v ≠ 0 →
      0 < (F.val.inChart e (e x) ![v, Complex.I • v]).re +
        (m : ℝ) * ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e (e x) v v := by
  simpa only [ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm_apply] using Compact.MetricDomination.compact_bilinear_positive_after_nat_multiple
    (fun x => ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm (F.val.inChart e (e x)))
    (fun x => ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e (e x)) hK
    ((smoothForm_metricInChart_continuous V F e he).mono hKe)
    (((ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_smooth V e he).continuousOn.comp e.continuousOn
      (fun _ hx => e.map_source hx)).mono hKe)
    (fun x hx v hv => ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_positive V e he (e.map_source (hKe hx)) v hv)

theorem smoothForm_metricInChart_at (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (x : V.analyticSpace) (hx : x ∈ e.source)
    (v : TangentSpace 𝓘(ℝ, V.analyticModel) x) :
    F.val.inChart e (e x) ![Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v, Complex.I • Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v] =
      F x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v] := by
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at _ e he x hx]
  apply congrArg (F x)
  funext j
  fin_cases j
  · exact (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx).symm_apply_apply v
  · rw [← Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul_inChart e he x hx Complex.I v]
    exact (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx).symm_apply_apply _

theorem smoothForm_positive_after_projective_multiple (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m → ∀ (x : V.analyticSpace)
      (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      0 < (F x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re +
        (m : ℝ) * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re := by
  classical
  obtain ⟨s, r, K, hcover, hK⟩ := CycleClass.Geometric.CompactChartCover.Cycles.exists_compact_chart_decomposition V.analyticModel
    (isCompact_univ : IsCompact (univ : Set V.analyticSpace))
  have hlocal (i : s) : ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m → ∀ x ∈ K i,
      ∀ v : V.analyticModel, v ≠ 0 →
      0 < (F.val.inChart (chartAt V.analyticModel i.val) (chartAt V.analyticModel i.val x)
        ![v, Complex.I • v]).re + (m : ℝ) *
          ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V (chartAt V.analyticModel i.val) (chartAt V.analyticModel i.val x) v v := by
    exact smoothForm_compactChart_positive_after_nat_multiple V F _
      (chart_mem_atlas V.analyticModel i.val) (hK i.val i.property).2.1
      ((hK i.val i.property).2.2.2.1.trans
        (CycleClass.Geometric.CompactChartCover.Cycles.chartClosedBallDomain_subset_source V.analyticModel i.val (r i.val)))
  choose n hn hbound using hlocal
  refine ⟨1 + ∑ i : s, n i, by omega, ?_⟩
  intro m hm x v hv
  have hx : x ∈ ⋃ i ∈ s, K i := by rw [← hcover]; trivial
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  let j : s := ⟨i, hi⟩
  have hnm : n j ≤ m := (Nat.le_add_left (n j) 1).trans
    ((Nat.add_le_add_left (Finset.single_le_sum (fun k _ => Nat.zero_le (n k))
      (Finset.mem_univ j)) 1).trans hm)
  let e := chartAt V.analyticModel i
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas _ i
  have hxe : x ∈ e.source :=
    CycleClass.Geometric.CompactChartCover.Cycles.chartClosedBallDomain_subset_source V.analyticModel i (r i)
      ((hK i hi).2.2.2.1 hxi)
  have hv' : Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v ≠ 0 := by
    intro hz
    exact hv ((Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hxe).injective
      (hz.trans (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hxe).map_zero.symm))
  have hp := hbound j m hnm x hxi (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v) hv'
  change 0 < (F.val.inChart e (e x) ![Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v, Complex.I • Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v]).re +
    (m : ℝ) * ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e (e x) (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v) (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v) at hp
  rw [ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart, ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm_apply, smoothForm_metricInChart_at V F e he x hxe v,
    smoothForm_metricInChart_at V (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V) e he x hxe v] at hp
  exact hp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CurvatureDomination
