import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovectorPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm

/-! # Open Form Metric -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.OpenFormMetric

noncomputable section

/-! The genuine projective covector metric pairs smooth open forms to an actual smooth scalar function. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {U : Opens V.analyticSpace} (n : ℕ)

theorem projectiveOpenFormMetricExpression_smooth
    (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    ContDiffOn ℝ ∞ (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveFormMetricExpression V e n a.extension b.extension)
      (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set V.analyticModel) := by
  let c := Module.finBasis ℝ V.analyticModel
  have hevala (s : Set.powersetCard (Fin (Module.finrank ℝ V.analyticModel)) n) :
      ContDiffOn ℝ ∞ (fun y => a.extension.inChart e y (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.exteriorCoordinateTuple V c n s))
        (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set V.analyticModel) := Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.smooth_fixed_form_evaluation n _ (a.smooth e he)
  have hevalb (s : Set.powersetCard (Fin (Module.finrank ℝ V.analyticModel)) n) :
      ContDiffOn ℝ ∞ (fun y => b.extension.inChart e y (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.exteriorCoordinateTuple V c n s))
        (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set V.analyticModel) := Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.smooth_fixed_form_evaluation n _ (b.smooth e he)
  have hcoeff (s t : Set.powersetCard (Fin (Module.finrank ℝ V.analyticModel)) n) :
      ContDiffOn ℝ ∞ (fun y => ((Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveExteriorGram V e c n y)⁻¹ s t : ℂ))
        (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set V.analyticModel) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveExteriorGram_inverse_smooth V e he c n s t).mono (fun _ hy => hy.1))
  have hconj : ContDiff ℝ ∞ (star : ℂ → ℂ) := Complex.conjCLE.contDiff
  unfold Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveFormMetricExpression
  change ContDiffOn ℝ ∞ (fun y => ∑ s, ∑ t,
    star (a.extension.inChart e y (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.exteriorCoordinateTuple V c n t)) *
      ((Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveExteriorGram V e c n y)⁻¹ s t : ℂ) *
        b.extension.inChart e y (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.exteriorCoordinateTuple V c n s)) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set V.analyticModel)
  fun_prop

theorem projectiveOpenFormPointPair_contMDiffOn (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n) :
    ContMDiffOn 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞
      (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.extension b.extension) (U : Set V.analyticSpace) := by
  intro x hx
  let e := chartAt V.analyticModel x
  have he := chart_mem_atlas V.analyticModel x
  have hex := mem_chart_source V.analyticModel x
  have hy : e x ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U := Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U hex hx
  have hF : ContMDiffAt 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞
      (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveFormMetricExpression V e n a.extension b.extension) (e x) :=
    ((projectiveOpenFormMetricExpression_smooth V n a b e he).contDiffAt
      ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hy)).contMDiffAt
  have he' : ContMDiffAt 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, V.analyticModel) ∞ e x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hex
  apply ContMDiffAt.contMDiffWithinAt
  apply (hF.comp x he').congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hex] with z hz
  have h := Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveFormPointPair_chartExpression V e he n a.extension b.extension (e z) (e.map_source hz)
  simpa only [Function.comp_apply, e.left_inv hz] using h

def projectiveOpenCovectorMetricFunction (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) U :=
  ⟨fun x => CovectorPair.projectiveTangentCovectorPair V n x.val (a x) (b x), by
    intro x
    have h := (projectiveOpenFormPointPair_contMDiffOn V n a b).contMDiffAt (U.isOpen.mem_nhds x.property)
    have hs := (contMDiffAt_subtype_iff (U := U) (x := x)).mpr h
    apply hs.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro y
    change CovectorPair.projectiveTangentCovectorPair V n y.val (a y) (b y) =
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.extension b.extension y.val
    rw [CovectorPair.projectiveFormPointPair_eq_tangentPair, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply,
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply]⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.OpenFormMetric
