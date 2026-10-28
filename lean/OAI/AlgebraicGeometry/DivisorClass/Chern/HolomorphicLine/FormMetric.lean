import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.FormPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.OpenFormMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm

/-! # Form Metric -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.FormMetric

noncomputable section

/-! The actual metric on line-bundle-valued smooth forms has smooth scalar pairings on every open. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

local instance lineFormMetric_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : FiniteDimensional ℝ V.analyticModel :=
  FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
  {U : Opens V.analyticSpace} (n : ℕ)

def holomorphicLineLocalFormMetricFunction (a b : AntiForms.HolomorphicLineSmoothForm u U n) (i : V.analyticSpace) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel)
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
  let w : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel)
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
    ⟨fun x => (MetricWeight.holomorphicLineMetricWeight u i ⟨x.val, x.property.2⟩ : ℂ),
      Complex.ofRealCLM.contDiff.contMDiff.comp
        ((HermitianPair.holomorphicLineMetricWeight_contMDiff u i).comp
          (contMDiff_inclusion (I := 𝓘(ℝ, V.analyticModel)) inf_le_right))⟩
  SmoothScalarForm.smoothComplexOpenFunctionMul w (Projective.OpenFormMetric.projectiveOpenCovectorMetricFunction V n (a.val i) (b.val i))

theorem holomorphicLineLocalFormMetricFunction_apply (a b : AntiForms.HolomorphicLineSmoothForm u U n)
    (i : V.analyticSpace) (x : ↥(U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    holomorphicLineLocalFormMetricFunction V u n a b i x =
      (MetricWeight.holomorphicLineMetricWeight u i ⟨x.val, x.property.2⟩ : ℂ) *
        Projective.CovectorPair.projectiveTangentCovectorPair V n x.val (a.val i x) (b.val i x) := rfl

theorem holomorphicLineSmoothFormPair_localExtension (a b : AntiForms.HolomorphicLineSmoothForm u U n)
    (i : V.analyticSpace) (x : U)
    (hi : x.val ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :
    FormPair.holomorphicLineSmoothFormPair V u n a b x =
      Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
        (holomorphicLineLocalFormMetricFunction V u n a b i) x.val := by
  rw [Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
      (holomorphicLineLocalFormMetricFunction V u n a b i) ⟨x.val, x.property, hi⟩,
    holomorphicLineLocalFormMetricFunction_apply]
  exact FormPair.holomorphicLineSmoothFormPair_inFrame V u n a b i x hi

theorem holomorphicLineSmoothFormPair_contMDiff (a b : AntiForms.HolomorphicLineSmoothForm u U n) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (FormPair.holomorphicLineSmoothFormPair V u n a b) := by
  intro x
  let i := x.val
  let D := Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  let W := U ⊓ D
  have hx : x.val ∈ D := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x.val
  let f := holomorphicLineLocalFormMetricFunction V u n a b i
  have hf : ContMDiffAt 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension W f) x.val :=
    (SmoothScalarForm.smoothOpenScalarExtension_contMDiffOn f).contMDiffAt (W.isOpen.mem_nhds ⟨x.property, hx⟩)
  apply (hf.comp x (contMDiff_subtype_val (I := 𝓘(ℝ, V.analyticModel)) (n := ∞)).contMDiffAt).congr_of_eventuallyEq
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds (D.isOpen.mem_nhds hx)] with y hy
  change y.val ∈ D at hy
  change FormPair.holomorphicLineSmoothFormPair V u n a b y = Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension W f y.val
  exact holomorphicLineSmoothFormPair_localExtension V u n a b i y hy

def holomorphicLineSmoothFormMetricFunction (a b : AntiForms.HolomorphicLineSmoothForm u U n) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) U :=
  ⟨FormPair.holomorphicLineSmoothFormPair V u n a b, holomorphicLineSmoothFormPair_contMDiff V u n a b⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.FormMetric
