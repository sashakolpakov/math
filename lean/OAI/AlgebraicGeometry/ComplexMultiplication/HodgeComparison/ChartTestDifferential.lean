import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction
import OAI.Analysis.DifferentialForms.Manifold.ManifoldLocallyFiniteSum

/-! # Chart Test Differential -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestDifferential.CM.Construction

noncomputable section

/-! The global chart test form has exactly the Euclidean test derivative,
and that derivative vanishes away from the original compact support. -/

open Set Filter
open scoped _root_.Manifold SchwartzMap _root_.Topology LineDeriv

variable {ι : Type*} [Fintype ι]

theorem varietyOneFormInChart_zero_at (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    {x : V.analyticSpace} (hx : x ∈ e.source) (hform : form x = 0) :
    GlobalLp.CM.Construction.varietyOneFormInChart V b e form x = 0 := by
  apply PiLp.ext
  intro i
  change form (e.symm (e x)) _ = 0
  rw [e.left_inv hx, hform]
  rfl

theorem varietyOneFormField_zero_at (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    {x : V.analyticSpace} (hform : form x = 0) : GlobalLp.CM.Construction.varietyOneFormField V C b form x = 0 := by
  obtain ⟨i, hi⟩ := C.exists_piece x
  change C.patchField _ x = 0
  rw [C.patchField_eq _ hi]
  exact varietyOneFormInChart_zero_at V b (C.chart i) form (C.piece_subset_source i hi) hform

theorem varietyChartTestForm_d_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {x : V.analyticSpace} (hx : x ∉ ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g)) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg) x = 0 := by
  have hzero : ChartTestFunction.CM.Construction.varietyChartTestScalar V e g =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (ChartTestFunction.CM.Construction.varietyChartTestScalar_tsupport V e g hgc hg h))
  have heq : ∀ᶠ y in 𝓝 x, (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg).val y =
      (0 : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0).val y := by
    filter_upwards [hzero] with y hy
    apply ContinuousAlternatingMap.ext
    intro v
    exact hy
  have hd := Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.exteriorDerivative_congr_eventually heq
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg) x =
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (0 : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) x at hd
  simpa only [map_zero, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.zero_apply] using hd

theorem varietyChartTestForm_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (i : ι) :
    GlobalLp.CM.Construction.varietyOneFormInChart V b e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg))
      (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) i = (∂_{b i} g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z := by
  rw [ScalarChartLocalization.CM.Construction.varietyScalarChart_differential V e he b _ (e.map_target hz), e.right_inv hz,
    ContinuousLinearEquiv.symm_apply_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have heq : ScalarChartLocalization.CM.Construction.varietyScalarChart V e (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg) =ᶠ[𝓝 z] g := by
    filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    exact ChartTestFunction.CM.Construction.varietyChartTestForm_in_chart V e he g hgc hg hy
  rw [heq.fderiv_eq]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestDifferential.CM.Construction
