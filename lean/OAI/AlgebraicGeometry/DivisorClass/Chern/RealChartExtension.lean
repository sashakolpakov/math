import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairSmooth
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction

/-! # Real Chart Extension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RealChartExtension

noncomputable section

section

/-! Compact smooth real coordinate functions extend to original global manifold functions with exact chart values. -/

open Set
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def projectiveRealChartExtension (f : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) : V.analyticSpace → ℝ :=
  e.source.indicator (fun x => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x))

theorem projectiveRealChartExtension_apply (f : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    {x : V.analyticSpace} (hx : x ∈ e.source) :
    projectiveRealChartExtension V e f x = f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x) := indicator_of_mem hx _

theorem projectiveRealChartExtension_zero (f : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    {x : V.analyticSpace} (hx : x ∉ e.source) : projectiveRealChartExtension V e f x = 0 :=
  indicator_of_notMem hx _

theorem projectiveRealChartExtension_inverse (f : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    projectiveRealChartExtension V e f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = f z := by
  rw [projectiveRealChartExtension_apply V e f (x := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) (e.map_target hz),
    Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hz]

theorem projectiveRealChartExtension_bound (f : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ z, f z ≤ C) (x : V.analyticSpace) :
    projectiveRealChartExtension V e f x ≤ C := by
  by_cases hx : x ∈ e.source
  · rw [projectiveRealChartExtension_apply V e f hx]
    exact hf _
  · rw [projectiveRealChartExtension_zero V e f hx]
    exact hC

include he

theorem projectiveRealChartExtension_smooth (f : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ) ∞ (projectiveRealChartExtension V e f) := by
  have hfc : HasCompactSupport (fun z => (f z : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hfs : ContDiff ℝ ∞ (fun z => (f z : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  let g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ) := hfc.toSchwartzMap hfs
  have hgs : tsupport g ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
    (tsupport_comp_subset Complex.ofReal_zero f).trans hs
  have hg := ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hfc hgs
  have heq : projectiveRealChartExtension V e f = (fun x => (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g x).re) := by
    funext x
    by_cases hx : x ∈ e.source
    · rw [projectiveRealChartExtension_apply V e f hx, ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar, indicator_of_mem hx]
      rfl
    · rw [projectiveRealChartExtension_zero V e f hx, ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar, indicator_of_notMem hx]
      rfl
  rw [heq]
  exact Complex.reCLM.contDiff.contMDiff.comp hg

end

/-! The actual compact real chart extension has support in the original compact chart image. -/

open Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction

theorem projectiveRealChartExtension_tsupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (f : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hc : HasCompactSupport f) (hs : tsupport f ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    tsupport (projectiveRealChartExtension V e f) ⊆ ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport f) := by
  apply closure_minimal ?_ (ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hc hs).isClosed
  intro x hx
  have hxe : x ∈ e.source := by
    by_contra he
    exact hx (projectiveRealChartExtension_zero V e f he)
  have hfx : f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x) ≠ 0 := by
    intro hf
    exact hx ((projectiveRealChartExtension_apply V e f hxe).trans hf)
  exact ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x, subset_tsupport f hfx, Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e x hxe⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RealChartExtension
