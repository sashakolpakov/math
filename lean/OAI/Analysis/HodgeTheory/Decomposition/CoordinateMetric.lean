import OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential

/-! # Coordinate Metric -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions

noncomputable section

/-! The actual form metric as a smooth positive operator in the fixed Hilbert
coordinates used for the exterior derivative and its formal adjoint. -/

open scoped BigOperators ContDiff _root_.Manifold

section Matrices

variable {I : Type*} [Fintype I]

def realMatrixOperator (A : Matrix I I ℝ) : EuclideanSpace ℂ I →L[ℝ] EuclideanSpace ℂ I :=
  ∑ s, ∑ t, A s t • (InnerProductSpace.rankOne ℂ (EuclideanSpace.basisFun I ℂ s)
    (EuclideanSpace.basisFun I ℂ t)).restrictScalars ℝ

theorem euclidean_real_inner_eq_re (u v : EuclideanSpace ℂ I) :
    inner ℝ u v = (inner ℂ u v).re := by
  change (∑ i, (inner ℂ (u i) (v i)).re) = (∑ i, inner ℂ (u i) (v i)).re
  exact (map_sum Complex.reCLM (fun i => inner ℂ (u i) (v i)) Finset.univ).symm

theorem realMatrixOperator_complex_inner (A : Matrix I I ℝ) (u v : EuclideanSpace ℂ I) :
    inner ℂ (realMatrixOperator A u) v =
      ∑ s, ∑ t, star (u t) * (A s t : ℂ) * v s := by
  simp only [realMatrixOperator, sum_apply, smul_apply]
  change inner ℂ (∑ s, ∑ t, (A s t : ℂ) •
    (InnerProductSpace.rankOne ℂ (EuclideanSpace.basisFun I ℂ s) (EuclideanSpace.basisFun I ℂ t) u)) v = _
  simp only [sum_inner, inner_smul_left, InnerProductSpace.rankOne_apply,
    EuclideanSpace.basisFun_inner]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  change star (A s t : ℂ) * (star (u t) * v s) = _
  rw [Complex.star_def, Complex.conj_ofReal]
  ring

theorem realMatrixOperator_smoothOn {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : D → Matrix I I ℝ) {U : Set D} (hA : ∀ s t, ContDiffOn ℝ ∞ (fun x => A x s t) U) :
    ContDiffOn ℝ ∞ (fun x => realMatrixOperator (A x)) U := by
  unfold realMatrixOperator
  fun_prop

end Matrices

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι ℝ V.analyticModel) (n : ℕ)

def projectiveCoordinateMetricOperator (y : V.analyticModel) :
    SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] SymbolDifferential.Constructions.ExteriorCoordinates ι n :=
  realMatrixOperator (MetricCoefficients.Constructions.projectiveExteriorGram V e b n y)⁻¹

theorem projectiveCoordinateMetric_inner (y : V.analyticModel) (hy : y ∈ e.target)
    (a c : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n) :
    inner ℝ (projectiveCoordinateMetricOperator V e b n y (SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a))
      (SymbolDifferential.Constructions.exteriorCoordinateEquiv b n c) = (ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a c).re := by
  rw [euclidean_real_inner_eq_re, projectiveCoordinateMetricOperator, realMatrixOperator_complex_inner,
    MetricCoefficients.Constructions.projectiveChartFormPair_coordinate_formula V e he b n y hy]
  simp only [SymbolDifferential.Constructions.exteriorCoordinateEquiv_apply, MetricCoefficients.Constructions.exteriorCoordinateTuple]

include he

theorem projectiveCoordinateMetric_smooth :
    ContDiffOn ℝ ∞ (projectiveCoordinateMetricOperator V e b n) e.target :=
  realMatrixOperator_smoothOn _ (MetricCoefficients.Constructions.projectiveExteriorGram_inverse_smooth V e he b n)

theorem projectiveCoordinateMetric_positive (y : V.analyticModel) (hy : y ∈ e.target)
    (u : SymbolDifferential.Constructions.ExteriorCoordinates ι n) (hu : u ≠ 0) :
    0 < inner ℝ (projectiveCoordinateMetricOperator V e b n y u) u := by
  let a := (SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm u
  have ha : SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a = u := (SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).apply_symm_apply u
  rw [← ha, projectiveCoordinateMetric_inner V e he b n y hy]
  have hnonneg : 0 ≤ (ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a a).re := ExteriorPair.Constructions.formMetricPair_nonneg n _
  by_contra hpos
  have hz : (ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a a).re = 0 :=
    le_antisymm (le_of_not_gt hpos) hnonneg
  have hz' : ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a a = 0 := by
    have hre : ((ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a a).re : ℂ) =
        ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a a := Form.Constructions.formMetricPair_self_re n _
    rw [← hre, hz, Complex.ofReal_zero]
  have ha0 := ProjectiveFormMetric.Constructions.projectiveChartFormPair_definite V e he y hy n a hz'
  apply hu
  rw [← ha, ha0, map_zero]

theorem projectiveCoordinateMetric_symmetric (y : V.analyticModel) (hy : y ∈ e.target)
    (u v : SymbolDifferential.Constructions.ExteriorCoordinates ι n) :
    inner ℝ (projectiveCoordinateMetricOperator V e b n y u) v =
      inner ℝ (projectiveCoordinateMetricOperator V e b n y v) u := by
  obtain ⟨a, rfl⟩ := (SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).surjective u
  obtain ⟨c, rfl⟩ := (SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).surjective v
  rw [projectiveCoordinateMetric_inner V e he b n y hy, projectiveCoordinateMetric_inner V e he b n y hy]
  have h := congrArg Complex.re (ExteriorPair.Constructions.formMetricPair_symm n
    (ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n a) (ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n c))
  change (star (ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n c a)).re =
    (ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a c).re at h
  simpa only [Complex.star_def, Complex.conj_re] using h.symm

end

end OAI.Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions
