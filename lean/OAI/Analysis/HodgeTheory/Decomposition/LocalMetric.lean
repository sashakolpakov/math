import OAI.Analysis.HodgeTheory.Decomposition.Form

/-! # Local Metric -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions

noncomputable section

/-! Local regularity and support of the actual pointwise form pairing. -/

open scoped ContDiff _root_.Manifold _root_.Topology BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)

theorem projectiveFormPointPair_congr_at
    (a b c d : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace)
    (hac : a x = c x) (hbd : b x = d x) :
    ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b x = ProjectiveFormMetric.Constructions.projectiveFormPointPair V n c d x := by
  let e := chartAt V.analyticModel x
  have he := chart_mem_atlas V.analyticModel x
  have hx := mem_chart_source V.analyticModel x
  have hac' : a.inChart e (e x) = c.inChart e (e x) := by
    ext v
    rw [DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at a e he x hx, DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at c e he x hx, hac]
  have hbd' : b.inChart e (e x) = d.inChart e (e x) := by
    ext v
    rw [DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at b e he x hx, DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at d e he x hx, hbd]
  unfold ProjectiveFormMetric.Constructions.projectiveFormPointPair
  rw [hac', hbd']

theorem projectiveFormPointPair_zero_left
    (b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace) :
    ProjectiveFormMetric.Constructions.projectiveFormPointPair V n 0 b x = 0 := by
  have h := Form.Constructions.projectiveFormPointPair_smul_left V n 0 b 0 x
  have hz : (0 : ℂ) • (0 : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) = 0 := by
    funext y
    exact zero_smul ℂ (0 : TangentSpace 𝓘(ℝ, V.analyticModel) y [⋀^Fin n]→L[ℝ] ℂ)
  rw [hz] at h
  simpa only [star_zero, zero_mul] using h

theorem projectiveFormPointPair_zero_right
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace) :
    ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a 0 x = 0 := by
  rw [← ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm, projectiveFormPointPair_zero_left, star_zero]

theorem projectiveFormPointPair_zero_of_right
    (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace)
    (hb : b x = 0) : ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b x = 0 :=
  (projectiveFormPointPair_congr_at V n a b a 0 x rfl hb).trans
    (projectiveFormPointPair_zero_right V n a x)

theorem projectiveFormMetricExpression_smooth_on
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a c : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    {S : Set V.analyticModel} (hS : S ⊆ e.target)
    (ha : ContDiffOn ℝ ∞ (a.inChart e) S) (hc : ContDiffOn ℝ ∞ (c.inChart e) S) :
    ContDiffOn ℝ ∞ (MetricCoefficients.Constructions.projectiveFormMetricExpression V e n a c) S := by
  let b := Module.finBasis ℝ V.analyticModel
  have hevala (s : Set.powersetCard (Fin (Module.finrank ℝ V.analyticModel)) n) :
      ContDiffOn ℝ ∞ (fun y => a.inChart e y (MetricCoefficients.Constructions.exteriorCoordinateTuple V b n s)) S :=
    MetricCoefficients.Constructions.smooth_fixed_form_evaluation n _ ha
  have hevalc (s : Set.powersetCard (Fin (Module.finrank ℝ V.analyticModel)) n) :
      ContDiffOn ℝ ∞ (fun y => c.inChart e y (MetricCoefficients.Constructions.exteriorCoordinateTuple V b n s)) S :=
    MetricCoefficients.Constructions.smooth_fixed_form_evaluation n _ hc
  have hcoeff (s t : Set.powersetCard (Fin (Module.finrank ℝ V.analyticModel)) n) :
      ContDiffOn ℝ ∞ (fun y => ((MetricCoefficients.Constructions.projectiveExteriorGram V e b n y)⁻¹ s t : ℂ)) S :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((MetricCoefficients.Constructions.projectiveExteriorGram_inverse_smooth V e he b n s t).mono hS)
  have hconj : ContDiff ℝ ∞ (star : ℂ → ℂ) := Complex.conjCLE.contDiff
  unfold MetricCoefficients.Constructions.projectiveFormMetricExpression
  change ContDiffOn ℝ ∞ (fun y => ∑ s, ∑ t,
    star (a.inChart e y (MetricCoefficients.Constructions.exteriorCoordinateTuple V b n t)) *
      ((MetricCoefficients.Constructions.projectiveExteriorGram V e b n y)⁻¹ s t : ℂ) *
      c.inChart e y (MetricCoefficients.Constructions.exteriorCoordinateTuple V b n s)) S
  fun_prop

theorem projectiveFormPointPair_continuousAt_of_smoothOn
    (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) {U : Set V.analyticSpace}
    (hU : IsOpen U) (ha : DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn a U) (hb : DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn b U)
    {x : V.analyticSpace} (hx : x ∈ U) : ContinuousAt (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b) x := by
  let e := chartAt V.analyticModel x
  have he := chart_mem_atlas V.analyticModel x
  have hxe := mem_chart_source V.analyticModel x
  have hdom : e x ∈ DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e U := by
    refine ⟨e.map_source hxe, ?_⟩
    change e.symm (e x) ∈ U
    simpa only [e.left_inv hxe] using hx
  have hc := (projectiveFormMetricExpression_smooth_on V n e he a b Set.inter_subset_left
    (ha e he) (hb e he)).continuousOn.continuousAt
      ((DifferentialForms.Manifold.Algebra.isOpen_manifoldFormChartDomain e hU).mem_nhds hdom)
  have hcomp : ContinuousAt (fun z => MetricCoefficients.Constructions.projectiveFormMetricExpression V e n a b (e z)) x :=
    hc.comp (e.continuousOn.continuousAt (e.open_source.mem_nhds hxe))
  apply hcomp.congr
  filter_upwards [e.open_source.mem_nhds hxe] with z hz
  have h := MetricCoefficients.Constructions.projectiveFormPointPair_chartExpression V e he n a b (e z) (e.map_source hz)
  simpa only [e.left_inv hz] using h.symm

/-- A locally smooth pairing with a supported smooth test form is continuous everywhere. -/
theorem projectiveFormPointPair_continuous_supported
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    {K U : Set V.analyticSpace} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (ha : DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn a U) (hb : ∀ x, x ∉ K → b x = 0) :
    Continuous (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b.val) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact projectiveFormPointPair_continuousAt_of_smoothOn V n a b.val hU ha
      (b.smooth.mono (Set.subset_univ _)) hx
  · have hxK : x ∈ Kᶜ := fun h => hx (hKU h)
    have hzero : ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b.val =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
      exact projectiveFormPointPair_zero_of_right V n a b.val y (hb y hy)
    exact continuousAt_const.congr hzero.symm

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions
