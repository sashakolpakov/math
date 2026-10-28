import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothScalarConstruction
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ScalarChartLocalization

/-! # Chart Test Function -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction

noncomputable section

/-! Compactly supported Euclidean test functions extend to actual global
smooth zero-forms, with their prescribed values in the original chart. -/

open Set Filter
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology

def varietyChartTestScalar (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) : V.analyticSpace → ℂ :=
  e.source.indicator (fun x => g ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)))

theorem varietyChartTestScalar_tsupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    tsupport (varietyChartTestScalar V e g) ⊆ ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g) := by
  apply closure_minimal ?_ (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hgc hg).isClosed
  intro x hx
  have hxs : x ∈ e.source := by
    by_contra h
    exact hx (indicator_of_notMem h _)
  have hval : g ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ≠ 0 := by
    change varietyChartTestScalar V e g x ≠ 0 at hx
    simpa only [varietyChartTestScalar, indicator_of_mem hxs] using hx
  refine ⟨(EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x), subset_closure hval, ?_⟩
  dsimp only
  rw [ContinuousLinearEquiv.apply_symm_apply, e.left_inv hxs]

theorem varietyChartTestScalar_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (varietyChartTestScalar V e g) := by
  intro x
  by_cases hx : x ∈ e.source
  · have heSmooth := (contMDiffOn_of_mem_maximalAtlas (n := ∞)
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, V.analyticModel)) he)).contMDiffAt (e.open_source.mem_nhds hx)
    have hL : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, EuclideanMetric.CM.Construction.varietyEuclideanModel V) ∞
        (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm :=
      ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.contMDiff
    have hcomp := (g.smooth ⊤).contMDiff.contMDiffAt.comp x (hL.contMDiffAt.comp x heSmooth)
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    change e.source.indicator (fun y => g ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e y))) y = _
    exact indicator_of_mem hy _
  · have hnot : x ∉ tsupport (varietyChartTestScalar V e g) := by
      intro hs
      exact hx (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hg (varietyChartTestScalar_tsupport V e g hgc hg hs))
    exact contMDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hnot)

def varietyChartTestForm (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 :=
  SmoothScalarConstruction.CM.Construction.scalarManifoldForm (varietyChartTestScalar V e g) (varietyChartTestScalar_smooth V e he g hgc hg)

theorem varietyChartTestForm_scalar (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    HolomorphicPrimitive.CM.Construction.zeroFormScalar (varietyChartTestForm V e he g hgc hg) = varietyChartTestScalar V e g := rfl

theorem varietyChartTestForm_in_chart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ScalarChartLocalization.CM.Construction.varietyScalarChart V e (varietyChartTestForm V e he g hgc hg) z = g z := by
  change varietyChartTestScalar V e g (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) = _
  rw [varietyChartTestScalar, indicator_of_mem (e.map_target hz), e.right_inv hz,
    ContinuousLinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction
