import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.SectionMetric
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Integral Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.IntegralPair

noncomputable section

/-! The actual Hermitian section pairing is integrable for the projective metric measure and has a positive definite integral. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartMeasure.CM.Construction

attribute [local instance] NormedSpace.complexToReal

local instance integralPair_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : FiniteDimensional ℝ V.analyticModel :=
  FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

def holomorphicLineGlobalSectionPair (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) : V.analyticSpace → ℂ :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension ⊤ (HolomorphicSmooth.SectionMetric.holomorphicLineSmoothSectionMetricFunction u s t)

theorem holomorphicLineGlobalSectionPair_apply (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0)
    (x : V.analyticSpace) :
    holomorphicLineGlobalSectionPair V u s t x = HolomorphicSmooth.SectionPair.holomorphicLineSmoothSectionPair u s t ⟨x, trivial⟩ :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply ⊤ (HolomorphicSmooth.SectionMetric.holomorphicLineSmoothSectionMetricFunction u s t) ⟨x, trivial⟩

theorem holomorphicLineGlobalSectionPair_contMDiff (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (holomorphicLineGlobalSectionPair V u s t) := by
  have h := SmoothScalarForm.smoothOpenScalarExtension_contMDiffOn (HolomorphicSmooth.SectionMetric.holomorphicLineSmoothSectionMetricFunction u s t)
  simpa only [holomorphicLineGlobalSectionPair, Opens.coe_top, contMDiffOn_univ] using h

theorem holomorphicLineGlobalSectionPair_integrable (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    Integrable (holomorphicLineGlobalSectionPair V u s t) (ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  apply integrableOn_univ.mp
  exact (holomorphicLineGlobalSectionPair_contMDiff V u s t).continuous.continuousOn.integrableOn_compact
    isCompact_univ

def holomorphicLineSectionIntegralPair (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) : ℂ :=
  ∫ x, holomorphicLineGlobalSectionPair V u s t x ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)

theorem holomorphicLineSectionIntegralPair_re (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    (holomorphicLineSectionIntegralPair V u s t).re =
      ∫ x, (holomorphicLineGlobalSectionPair V u s t x).re ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  (integral_re (holomorphicLineGlobalSectionPair_integrable V u s t)).symm

theorem holomorphicLineSectionIntegralPair_nonneg (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    0 ≤ (holomorphicLineSectionIntegralPair V u s s).re := by
  rw [holomorphicLineSectionIntegralPair_re]
  apply integral_nonneg
  intro x
  change 0 ≤ (holomorphicLineGlobalSectionPair V u s s x).re
  rw [holomorphicLineGlobalSectionPair_apply]
  exact HolomorphicSmooth.SectionPair.holomorphicLineSmoothSectionPair_nonneg u s ⟨x, trivial⟩

theorem holomorphicLineSectionIntegralPair_definite (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0)
    (hs : (holomorphicLineSectionIntegralPair V u s s).re = 0) : s = 0 := by
  have hn : 0 ≤ fun x => (holomorphicLineGlobalSectionPair V u s s x).re := by
    intro x
    change 0 ≤ (holomorphicLineGlobalSectionPair V u s s x).re
    rw [holomorphicLineGlobalSectionPair_apply]
    exact HolomorphicSmooth.SectionPair.holomorphicLineSmoothSectionPair_nonneg u s ⟨x, trivial⟩
  rw [holomorphicLineSectionIntegralPair_re] at hs
  have hae := (integral_eq_zero_iff_of_nonneg hn
    (holomorphicLineGlobalSectionPair_integrable V u s s).re).mp hs
  have hcont : Continuous (fun x => (holomorphicLineGlobalSectionPair V u s s x).re) :=
    Complex.continuous_re.comp (holomorphicLineGlobalSectionPair_contMDiff V u s s).continuous
  have hz := Measure.eq_of_ae_eq hae hcont continuous_const
  apply HolomorphicSmooth.SectionPair.holomorphicLineSmoothSectionPair_definite u s
  intro x
  have hx := congrFun hz x.val
  rw [holomorphicLineGlobalSectionPair_apply] at hx
  exact hx

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.IntegralPair
