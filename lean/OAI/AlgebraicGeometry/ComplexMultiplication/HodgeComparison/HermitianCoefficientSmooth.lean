import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricCoefficientDivergence

/-! # Hermitian Coefficient Smooth -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianCoefficientSmooth.CM.Construction

noncomputable section

/-! Smooth fixed-coordinate inverse-Hermitian coefficients and the actual
density-weighted coefficients used by the one-form adjoint. -/

open scoped ContDiff

section Matrix

variable {E ι 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [DecidableEq ι] [RCLike 𝕜] {U : Set E}

theorem matrix_determinant_smoothOn (M : E → Matrix ι ι 𝕜)
    (hM : ∀ i j, ContDiffOn ℝ ∞ (fun x => M x i j) U) :
    ContDiffOn ℝ ∞ (fun x => (M x).det) U := by
  simp only [Matrix.det_apply']
  fun_prop

theorem matrix_inverse_smoothOn (M : E → Matrix ι ι 𝕜)
    (hM : ∀ i j, ContDiffOn ℝ ∞ (fun x => M x i j) U)
    (hdet : ∀ x ∈ U, (M x).det ≠ 0) (i j : ι) :
    ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ i j) U := by
  have hd := (matrix_determinant_smoothOn M hM).inv hdet
  have ha : ContDiffOn ℝ ∞ (fun x => (M x).adjugate i j) U := by
    simp only [Matrix.adjugate_apply]
    apply matrix_determinant_smoothOn
    intro k l
    by_cases hkj : k = j
    · subst k
      simpa only [Matrix.updateRow_self] using
        (contDiffOn_const (c := (Pi.single i 1 : ι → 𝕜) l))
    · simpa only [Matrix.updateRow_ne hkj] using hM k l
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact hd.mul ha

end Matrix

theorem varietyHermitianMatrix_inverse_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V.analyticModel) (i j : ι) :
    ContDiffOn ℝ ∞ (fun y => (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y)⁻¹ i j) e.target :=
  matrix_inverse_smoothOn _ (fun i j => Analysis.HodgeTheory.Decomposition.Hermitian.Constructions.projectiveMetricHermitian_smooth V e he (b i) (b j))
    (fun _ hy => (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_det_isUnit V e he b hy).ne_zero) i j

def varietyWeightedHermitianInverse (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Matrix (Fin V.complexDimension) (Fin V.complexDimension) ℂ :=
  (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) •
    (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹

theorem varietyWeightedHermitianInverse_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (i j : Fin V.complexDimension) :
    ContDiffOn ℝ ∞ (fun z => varietyWeightedHermitianInverse V e z i j)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) := by
  have hρ := Complex.ofRealCLM.contDiff.comp_contDiffOn (Metric.CM.Construction.varietyMetricDensity_smooth V e he)
  have hP := (varietyHermitianMatrix_inverse_smooth V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) i j).comp
    ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ).contDiffOn
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates_mapsTo V e)
  exact hρ.mul hP

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianCoefficientSmooth.CM.Construction
