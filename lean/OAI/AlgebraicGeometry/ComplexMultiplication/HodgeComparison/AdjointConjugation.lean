import OAI.Analysis.HodgeTheory.Decomposition.AdjointAlgebra
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricMeasure
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation

/-! # Adjoint Conjugation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointConjugation.CM.Construction

noncomputable section

section

/-! The independently constructed formal-adjoint volume is the same
actual projective metric measure used by the scalar Poisson solver. -/

open _root_.MeasureTheory

theorem varietyMetricChartMeasure_eq_adjoint_measure (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V e = Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveChartMeasure V e := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_lintegral V e he f hf,
    Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveChartMeasure_lintegral V e he f hf]

theorem adjoint_metric_volume_eq (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V = GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
  apply GlobalMetricMeasure.CM.Construction.varietyMetricMeasure_unique V
  intro e he
  rw [Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume_restrict V e he,
    ← varietyMetricChartMeasure_eq_adjoint_measure V e he,
    MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_restrict_source]

end

/-! Complex conjugation preserves the genuine metric and commutes with
the global codifferential. -/

open _root_.MeasureTheory

section Fiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem covectorInner_conjugate (f g : E →ₗ[ℝ] ℂ) :
    Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner (Complex.conjCLE.toLinearMap.comp f) (Complex.conjCLE.toLinearMap.comp g) =
      star (Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner f g) := by
  change (∑ i, star (star (f (stdOrthonormalBasis ℝ E i))) *
    star (g (stdOrthonormalBasis ℝ E i))) =
    star (∑ i, star (f (stdOrthonormalBasis ℝ E i)) * g (stdOrthonormalBasis ℝ E i))
  simp only [star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem exteriorCovector_conjugate (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap a) =
      Complex.conjCLE.toLinearMap.comp (Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n a) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_apply_ιMulti, LinearMap.comp_apply]
  rfl

theorem formMetricPair_conjugate (n : ℕ) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap a)
      (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap c) =
      star (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n a c) := by
  rw [Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair, exteriorCovector_conjugate, exteriorCovector_conjugate]
  exact covectorInner_conjugate _ _

end Fiber

theorem projectiveChartPair_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (y : V.analyticModel) (hy : y ∈ e.target)
    (n : ℕ) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel n) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n
      (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap a)
      (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap c) =
      star (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a c) := by
  exact formMetricPair_conjugate n
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n a) (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n c)

theorem projectivePointPair_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a c : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (Conjugation.CM.Construction.conjugateRawForm a) (Conjugation.CM.Construction.conjugateRawForm c) x =
      star (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a c x) := by
  rw [Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair, Conjugation.CM.Construction.conjugateRawForm_inChart, Conjugation.CM.Construction.conjugateRawForm_inChart]
  exact projectiveChartPair_conjugate V _ _ _ _ n _ _

theorem projectiveL2Pair_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V n (Conjugation.CM.Construction.conjugateSmoothForm a) (Conjugation.CM.Construction.conjugateSmoothForm c) =
      star (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V n a c) := by
  change (∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (Conjugation.CM.Construction.conjugateRawForm a.val) (Conjugation.CM.Construction.conjugateRawForm c.val) x
    ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V) =
    starRingEnd ℂ (∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val c.val x ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V)
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (projectivePointPair_conjugate V n a.val c.val)

theorem projectiveCodifferential_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V n (Conjugation.CM.Construction.conjugateSmoothForm a) =
      Conjugation.CM.Construction.conjugateSmoothForm (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V n a) := by
  apply Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveL2Pair_separates_left V n
  intro c
  have h := congrArg (star : ℂ → ℂ)
    (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential_pair V n (Conjugation.CM.Construction.conjugateSmoothForm c) a)
  rw [← projectiveL2Pair_conjugate, ← projectiveL2Pair_conjugate,
    ← Conjugation.CM.Construction.d_conjugateSmoothForm, Conjugation.CM.Construction.conjugateSmoothForm_involutive] at h
  rw [← Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential_pair]
  exact h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointConjugation.CM.Construction
