import OAI.Analysis.HodgeTheory.Decomposition.CovariantAdjointPair
import OAI.Analysis.HodgeTheory.Decomposition.EuclideanBilinearMetric
import OAI.Analysis.HodgeTheory.Decomposition.FormalAdjointPairDerivative
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth

/-! # Projective Covariant Numerator -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovariantNumerator.Constructions

noncomputable section

/-! The actual projective formal-adjoint numerator is the weighted metric
applied to the covariant codifferential, including every lower-order term. -/

open scoped ContDiff

theorem complex_fderiv_re_apply {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : D → ℂ) {x : D} (hf : DifferentiableAt ℝ f x) (u : D) :
    fderiv ℝ (fun y => (f y).re) x u = (fderiv ℝ f x u).re := by
  have h := Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt
  exact congrArg (fun L : D →L[ℝ] ℝ => L u) h.fderiv

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

theorem projectiveFormalAdjointNumerator_covariant
    (a : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1))
    (ha : ContDiffOn ℝ ∞ a (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _))
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    LocalAdjoint.Constructions.formalAdjointNumerator (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n) (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1))
      (fun y => SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis (n + 1) (a y)) z =
    AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
      (SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (CovariantAdjointPair.Constructions.bilinearCovariantCodifferential (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
          (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) a z)) := by
  let b := (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let Q := SymbolDifferential.Constructions.exteriorCoordinateEquiv b n
  let P := SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)
  have had := (ha.contDiffAt ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hB := ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).contDiffAt
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hρ := ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).contDiffAt
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hM := ((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he (n + 1)).contDiffAt
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hPa : DifferentiableAt ℝ (fun y => P (a y)) z :=
    (P.toContinuousLinearMap.restrictScalars ℝ).differentiableAt.comp z had
  apply ext_inner_right ℝ
  intro v
  obtain ⟨c, rfl⟩ := Q.surjective v
  rw [FormalAdjointPairDerivative.Constructions.formalAdjointNumerator_pair_derivative _ _ _ _ hM hPa,
    EuclideanBilinearMetric.Constructions.projectiveWeightedFormOperator_bilinear_pair]
  let F (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (y : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e y : ℂ) * BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e y)
      (a y) (SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c)
  have hF (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) : DifferentiableAt ℝ (F i) z := by
    have hp := WeightedMetricDerivative.Constructions.bilinearFormMetricPair_differentiableAt b (n + 1) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
      a (fun _ => SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c) hB had
      (differentiableAt_const _) (BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b (n + 1) _
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz))
    exact (Complex.ofRealCLM.differentiableAt.comp z hρ).mul hp
  have hI (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) :
      (fun y => inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) y (P (a y)))
        (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i (Q c))) = (fun y => (F i y).re) := by
    funext y
    change inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) y (P (a y)))
      (P (SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap (Q.symm (Q c)))) = _
    rw [Q.symm_apply_apply]
    exact EuclideanBilinearMetric.Constructions.projectiveWeightedFormOperator_bilinear_pair V e (n + 1) y _ _
  simp_rw [hI, complex_fderiv_re_apply _ (hF _)]
  have hsum := CovariantAdjointPair.Constructions.covariantAdjointPair_derivative_sum b n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) a c hB had hρ
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
    (ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hz) (ProjectiveConnection.Constructions.projectiveConnectionCoefficient_symmetric V e he hz)
  have hr := congrArg Complex.re hsum
  rw [Complex.re_sum] at hr
  change (∑ i, (fderiv ℝ (F i) z (b i)).re) = _ at hr
  change -(∑ i, (fderiv ℝ (F i) z (b i)).re) = _
  rw [hr]
  simp only [neg_mul, Complex.neg_re, neg_neg]
  rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovariantNumerator.Constructions
