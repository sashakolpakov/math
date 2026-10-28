import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.SectionPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothZeroFormFunctions

/-! # Section Metric -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.SectionMetric

noncomputable section

/-! The frame-independent Hermitian pairing of actual smooth line-bundle sections is a genuine smooth scalar function. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [CompactSpace M] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) {U : Opens M}

def holomorphicLineLocalSmoothSectionPair (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) (i : M) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :=
  let w : SmoothScalarForm.SmoothComplexOpenFunction (E := E) (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :=
    ⟨fun x => (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i ⟨x.val, x.property.2⟩ : ℂ),
      Complex.ofRealCLM.contDiff.contMDiff.comp
        ((HolomorphicLine.HermitianPair.holomorphicLineMetricWeight_contMDiff u i).comp
          (contMDiff_inclusion (I := 𝓘(ℝ, E)) inf_le_right))⟩
  SmoothScalarForm.smoothComplexOpenFunctionMul
    (SmoothScalarForm.smoothComplexOpenFunctionMul w (SmoothHolomorphicScalar.conjugateSmoothOpenFunction (SmoothZeroFormFunctions.smoothManifoldZeroFunction (s.val i))))
    (SmoothZeroFormFunctions.smoothManifoldZeroFunction (t.val i))

theorem holomorphicLineLocalSmoothSectionPair_apply (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0)
    (i : M) (x : ↥(U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)) :
    holomorphicLineLocalSmoothSectionPair u s t i x =
      HolomorphicLine.HermitianPair.holomorphicLineHermitianPair u i ⟨x.val, x.property.2⟩ (s.val i x 0) (t.val i x 0) := rfl

theorem holomorphicLineSmoothSectionPair_contMDiff (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (SectionPair.holomorphicLineSmoothSectionPair u s t) := by
  intro x
  let i := x.val
  let D := Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i
  let W := U ⊓ D
  have hx : x.val ∈ D := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x.val
  let f := holomorphicLineLocalSmoothSectionPair u s t i
  have hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension W f) x.val :=
    (SmoothScalarForm.smoothOpenScalarExtension_contMDiffOn f).contMDiffAt (W.isOpen.mem_nhds ⟨x.property, hx⟩)
  apply (hf.comp x (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)).contMDiffAt).congr_of_eventuallyEq
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds (D.isOpen.mem_nhds hx)] with y hy
  change y.val ∈ D at hy
  change SectionPair.holomorphicLineSmoothSectionPair u s t y = Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension W f y.val
  rw [Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply W f ⟨y.val, y.property, hy⟩]
  exact SectionPair.holomorphicLineSmoothSectionPair_inFrame u s t i y hy

def holomorphicLineSmoothSectionMetricFunction (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) U :=
  ⟨SectionPair.holomorphicLineSmoothSectionPair u s t, holomorphicLineSmoothSectionPair_contMDiff u s t⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.SectionMetric
