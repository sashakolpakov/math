import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.FormMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.InnerProduct

/-! # Form Integral Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormIntegralPair

noncomputable section

/-! The actual projective metric integral defines a positive inner product on line-bundle-valued forms in every degree. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (n : ℕ)

def holomorphicLineGlobalFormPair (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) : V.analyticSpace → ℂ :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension ⊤ (HolomorphicLine.FormMetric.holomorphicLineSmoothFormMetricFunction V u n a b)

theorem holomorphicLineGlobalFormPair_apply (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : V.analyticSpace) :
    holomorphicLineGlobalFormPair V u n a b x = HolomorphicLine.FormPair.holomorphicLineSmoothFormPair V u n a b ⟨x, trivial⟩ :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply ⊤ (HolomorphicLine.FormMetric.holomorphicLineSmoothFormMetricFunction V u n a b) ⟨x, trivial⟩

theorem holomorphicLineGlobalFormPair_contMDiff (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (holomorphicLineGlobalFormPair V u n a b) := by
  have h := SmoothScalarForm.smoothOpenScalarExtension_contMDiffOn (HolomorphicLine.FormMetric.holomorphicLineSmoothFormMetricFunction V u n a b)
  simpa only [holomorphicLineGlobalFormPair, Opens.coe_top, contMDiffOn_univ] using h

theorem holomorphicLineGlobalFormPair_integrable (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    Integrable (holomorphicLineGlobalFormPair V u n a b) (ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  apply integrableOn_univ.mp
  exact (holomorphicLineGlobalFormPair_contMDiff V u n a b).continuous.continuousOn.integrableOn_compact
    isCompact_univ

def holomorphicLineFormIntegralPair (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) : ℂ :=
  ∫ x, holomorphicLineGlobalFormPair V u n a b x ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)

theorem holomorphicLineFormIntegralPair_re (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (holomorphicLineFormIntegralPair V u n a b).re =
      ∫ x, (holomorphicLineGlobalFormPair V u n a b x).re ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  (integral_re (holomorphicLineGlobalFormPair_integrable V u n a b)).symm

theorem holomorphicLineFormIntegralPair_conj (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    conj (holomorphicLineFormIntegralPair V u n b a) = holomorphicLineFormIntegralPair V u n a b := by
  unfold holomorphicLineFormIntegralPair
  rw [← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [holomorphicLineGlobalFormPair_apply, HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_conj]

theorem holomorphicLineFormIntegralPair_add_left (a b c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    holomorphicLineFormIntegralPair V u n (a + b) c =
      holomorphicLineFormIntegralPair V u n a c + holomorphicLineFormIntegralPair V u n b c := by
  calc
    _ = ∫ x, (holomorphicLineGlobalFormPair V u n a c x + holomorphicLineGlobalFormPair V u n b c x)
        ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [holomorphicLineGlobalFormPair_apply, HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_add_left]
    _ = _ := integral_add (holomorphicLineGlobalFormPair_integrable V u n a c)
      (holomorphicLineGlobalFormPair_integrable V u n b c)

theorem holomorphicLineFormIntegralPair_smul_left (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (z : ℂ) :
    holomorphicLineFormIntegralPair V u n (z • a) b = conj z * holomorphicLineFormIntegralPair V u n a b := by
  calc
    _ = ∫ x, conj z * holomorphicLineGlobalFormPair V u n a b x ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [holomorphicLineGlobalFormPair_apply, HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_smul_left]
    _ = _ := integral_const_mul (conj z) _

theorem holomorphicLineFormIntegralPair_nonneg (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    0 ≤ (holomorphicLineFormIntegralPair V u n a a).re := by
  rw [holomorphicLineFormIntegralPair_re]
  apply integral_nonneg
  intro x
  change 0 ≤ (holomorphicLineGlobalFormPair V u n a a x).re
  rw [holomorphicLineGlobalFormPair_apply]
  exact HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_nonneg V u n a ⟨x, trivial⟩

theorem holomorphicLineFormIntegralPair_definite (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (ha : (holomorphicLineFormIntegralPair V u n a a).re = 0) : a = 0 := by
  have hn : 0 ≤ fun x => (holomorphicLineGlobalFormPair V u n a a x).re := by
    intro x
    change 0 ≤ (holomorphicLineGlobalFormPair V u n a a x).re
    rw [holomorphicLineGlobalFormPair_apply]
    exact HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_nonneg V u n a ⟨x, trivial⟩
  rw [holomorphicLineFormIntegralPair_re] at ha
  have hae := (integral_eq_zero_iff_of_nonneg hn
    (holomorphicLineGlobalFormPair_integrable V u n a a).re).mp ha
  have hc : Continuous (fun x => (holomorphicLineGlobalFormPair V u n a a x).re) :=
    Complex.continuous_re.comp (holomorphicLineGlobalFormPair_contMDiff V u n a a).continuous
  have hz := Measure.eq_of_ae_eq hae hc continuous_const
  apply HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_definite V u n a
  intro x
  have hx := congrFun hz x.val
  rw [holomorphicLineGlobalFormPair_apply] at hx
  exact hx

@[instance_reducible]
def holomorphicLineFormInnerProductCore : InnerProductSpace.Core ℂ (HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) where
  inner := holomorphicLineFormIntegralPair V u n
  conj_inner_symm := holomorphicLineFormIntegralPair_conj V u n
  re_inner_nonneg := holomorphicLineFormIntegralPair_nonneg V u n
  add_left := holomorphicLineFormIntegralPair_add_left V u n
  smul_left := holomorphicLineFormIntegralPair_smul_left V u n
  definite a ha := holomorphicLineFormIntegralPair_definite V u n a (congrArg Complex.re ha)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormIntegralPair
