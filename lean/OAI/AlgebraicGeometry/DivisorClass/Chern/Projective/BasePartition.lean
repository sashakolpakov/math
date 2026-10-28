import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.FrameScalarGlue
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarExterior
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.MetricWeight

/-! # Base Partition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BasePartition

noncomputable section

section

/-! Literal Euclidean coordinates and derivatives of original smooth scalar functions on projective opens. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def projectiveScalarChart (U : Opens V.analyticSpace)
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) U) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))

theorem projectiveScalarChart_apply (U : Opens V.analyticSpace)
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) U) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    projectiveScalarChart V e U f z = f ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩ :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U f ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩

theorem projectiveOpenChartForm_restrict {U W : Opens V.analyticSpace} (hWU : W ≤ U)
    (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e W) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hWU a).extension z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n a.extension z := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  rw [Open.ManifoldBidegree.openManifold_restrict_inChart hWU a e hz.2]

include he

theorem projectiveScalarChart_smooth (U : Opens V.analyticSpace)
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) U) :
    ContDiffOn ℝ ∞ (projectiveScalarChart V e U f) (ConnectionChartDerivative.projectiveOpenChartDomain V e U : Set _) :=
  (SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff f e he).comp
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ).contDiffOn (fun _ hz => hz)

theorem projectiveScalarChart_derivative (U : Opens V.analyticSpace)
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) U) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    AntiOneFormCoordinates.oneFormLinear (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)).extension z) v =
      fderiv ℝ (projectiveScalarChart V e U f) z v := by
  have hf := ((SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff f e he).contDiffAt
    ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hd := congrArg (fun T : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℂ => T v)
    (hf.hasFDerivAt.comp z ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).fderiv
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  rw [SmoothScalarExterior.smoothScalarOpenZeroForm_d_inChart f e he hz]
  exact hd.symm

end

/-! A fixed finite smooth partition in the original projective base charts, independent of all line bundles and twists. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

local instance basePartition_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : FiniteDimensional ℝ V.analyticModel :=
  FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem exists_projectiveBaseFiniteCover : ∃ s : Finset V.analyticSpace,
    ∀ x : V.analyticSpace, ∃ i : s, x ∈ (chartAt V.analyticModel i.val).source := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i : V.analyticSpace => (chartAt V.analyticModel i).source)
    (fun i => (chartAt V.analyticModel i).open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source V.analyticModel x⟩)
  refine ⟨s, ?_⟩
  intro x
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact ⟨⟨i, hi⟩, hxi⟩

def projectiveBaseFiniteCover : Finset V.analyticSpace := (exists_projectiveBaseFiniteCover V).choose

theorem projectiveBaseFiniteCover_covers (x : V.analyticSpace) :
    ∃ i : projectiveBaseFiniteCover V, x ∈ (chartAt V.analyticModel i.val).source :=
  (exists_projectiveBaseFiniteCover V).choose_spec x

theorem exists_projectiveBaseSmoothPartition :
    ∃ p : SmoothPartitionOfUnity (projectiveBaseFiniteCover V) 𝓘(ℝ, V.analyticModel) V.analyticSpace,
      p.IsSubordinate (fun i => (chartAt V.analyticModel i.val).source) := by
  apply SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, V.analyticModel) isClosed_univ
    (fun i : projectiveBaseFiniteCover V => (chartAt V.analyticModel i.val).source)
    (fun i => (chartAt V.analyticModel i.val).open_source)
  intro x _
  exact mem_iUnion.mpr (projectiveBaseFiniteCover_covers V x)

def projectiveBaseSmoothPartition :
    SmoothPartitionOfUnity (projectiveBaseFiniteCover V) 𝓘(ℝ, V.analyticModel) V.analyticSpace :=
  (exists_projectiveBaseSmoothPartition V).choose

theorem projectiveBaseSmoothPartition_support (i : projectiveBaseFiniteCover V) :
    tsupport (projectiveBaseSmoothPartition V i) ⊆ (chartAt V.analyticModel i.val).source :=
  (exists_projectiveBaseSmoothPartition V).choose_spec i

theorem projectiveBaseSmoothPartition_smooth (i : projectiveBaseFiniteCover V) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ) ∞ (projectiveBaseSmoothPartition V i) :=
  (projectiveBaseSmoothPartition V i).contMDiff

theorem projectiveBaseSmoothPartition_sum (x : V.analyticSpace) :
    ∑ i, projectiveBaseSmoothPartition V i x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using (projectiveBaseSmoothPartition V).sum_eq_one (mem_univ x)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BasePartition
