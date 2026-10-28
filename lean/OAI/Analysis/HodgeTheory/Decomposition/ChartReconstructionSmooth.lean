import OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzLocalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence

/-! # Chart Reconstruction Smooth -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ChartReconstructionSmooth.Constructions

noncomputable section

section

/-! Actual chart reconstruction of localized smooth coefficients is
ordinary multiplication of the original manifold form by the chart cutoff. -/

open scoped SchwartzMap ContDiff _root_.Manifold
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

theorem varietyChartTestScalar_inverse
    (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g (MeasureVolume.Constructions.chartCoordinateInverse V e z) = g z := by
  change e.source.indicator (fun x => g ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)))
    (e.symm (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) = _
  rw [Set.indicator_of_mem (e.map_target hz), e.right_inv hz, ContinuousLinearEquiv.symm_apply_apply]

theorem supportedEuclideanCoefficients_chart_smul
    (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) a) z =
      g z • SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a z := by
  by_cases hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
  · rw [SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n _ hz, SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n a hz,
      ChartTestForms.Constructions.euclideanChartCoefficients_smulFunction, varietyChartTestScalar_inverse V e g z hz]
  · rw [show SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
        (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) a) z = 0 from Set.indicator_of_notMem hz _,
      show SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a z = 0 from Set.indicator_of_notMem hz _, smul_zero]

variable (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport g)
  (hgs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (χ : V.analyticSpace → ℝ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ χ)
  (hχs : tsupport χ ⊆ e.source)

theorem projectiveSchwartzTestLocalized_localization
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hgc hgs
      (SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he n χ hχ hχs a) =
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g)
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hgc hgs) (RealMultiplier.Constructions.projectiveRealMultiplier V n χ hχ a) := by
  apply Subtype.ext
  apply ChartCoefficientFaithful.Constructions.supportedCoefficients_faithful V e he n
  · exact ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_zero_off_source V e he n g hgc hgs _
  · intro x hx
    change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g x • RealMultiplier.Constructions.projectiveRealMultiplier V n χ hχ a x = 0
    rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar, Set.indicator_of_notMem hx]
    exact zero_smul ℂ (RealMultiplier.Constructions.projectiveRealMultiplier V n χ hχ a x)
  · intro z
    rw [ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_coefficients]
    change g z • SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (RealMultiplier.Constructions.projectiveRealMultiplier V n χ hχ a).val z =
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
        (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) (RealMultiplier.Constructions.projectiveRealMultiplier V n χ hχ a).val) z
    exact (supportedEuclideanCoefficients_chart_smul V e n g _ z).symm

end

/-! Every genuine smooth real manifold cutoff supported in one chart
comes from a compact scalar Schwartz cutoff in that chart. -/

open Set
open scoped SchwartzMap ContDiff _root_.Manifold
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction

theorem exists_projective_chart_scalar_cutoff (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (ρ : V.analyticSpace → ℝ) (hρ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ ρ)
    (hρs : tsupport ρ ⊆ e.source) :
    ∃ β : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport β ∧
      tsupport β ⊆ MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport ρ ∧
      tsupport β ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e β = (fun x => (ρ x : ℂ)) := by
  let K := MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport ρ
  have hK : IsCompact K := SupportedCoordinates.Constructions.chartCoordinateForward_compact V e (isClosed_tsupport ρ).isCompact hρs
  have hKU : K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    rintro _ ⟨x, hx, rfl⟩
    exact MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hρs hx)
  obtain ⟨ψ, hψc, hψU, _hψreal, hψnear⟩ :=
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact hK (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hKU
  let φ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothScalarConstruction.CM.Construction.scalarManifoldForm (fun x => (ρ x : ℂ)) (RealMultiplier.Constructions.projectiveRealFunction_complex_smooth V ρ hρ)
  let β := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he ψ hψc hψU φ
  have hβ (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
      β z = (ρ (MeasureVolume.Constructions.chartCoordinateInverse V e z) : ℂ) := by
    change ψ z * (ρ (MeasureVolume.Constructions.chartCoordinateInverse V e z) : ℂ) = _
    by_cases hzero : ρ (MeasureVolume.Constructions.chartCoordinateInverse V e z) = 0
    · rw [hzero, Complex.ofReal_zero, mul_zero]
    · have hzK : z ∈ K := ⟨MeasureVolume.Constructions.chartCoordinateInverse V e z, subset_tsupport ρ hzero,
        MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hz⟩
      rw [(hψnear z hzK).eq_of_nhds]
      exact one_mul _
  have hβzero (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∉ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : β z = 0 := by
    change ψ z * AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ScalarChartLocalization.CM.Construction.varietyScalarChart V e φ z = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hψU h)), zero_mul]
  have hβK : tsupport β ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    have hzU : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
      by_contra h
      exact hz (hβzero z h)
    have hρz : ρ (MeasureVolume.Constructions.chartCoordinateInverse V e z) ≠ 0 := by
      intro h
      apply hz
      rw [hβ z hzU, h, Complex.ofReal_zero]
    exact ⟨MeasureVolume.Constructions.chartCoordinateInverse V e z, subset_tsupport ρ hρz, MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hzU⟩
  refine ⟨β, hK.of_isClosed_subset (isClosed_tsupport _) hβK, hβK, hβK.trans hKU, ?_⟩
  funext x
  by_cases hx : x ∈ e.source
  · change e.source.indicator (fun y => β (MeasureVolume.Constructions.chartCoordinateForward V e y)) x = _
    rw [indicator_of_mem hx, hβ _ (MeasureVolume.Constructions.chartCoordinateForward_mem V e x hx),
      MeasureVolume.Constructions.chartCoordinateInverse_forward V e x hx]
  · rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar, indicator_of_notMem hx,
      image_eq_zero_of_notMem_tsupport (fun h => hx (hρs h)), Complex.ofReal_zero]

end

end OAI.Analysis.HodgeTheory.Decomposition.ChartReconstructionSmooth.Constructions
