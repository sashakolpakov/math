import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicTwoCoefficient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoChartMetric

/-! # Two Metric -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoMetric.Closedness

noncomputable section

/-! The exact projective metric contraction for (2,0) two-forms. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoChartMetric.CM.Construction

section Coefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem holomorphicTwoCoefficient_pair (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 f) (u v : E) :
    ComplexMultiplication.HodgeComparison.MixedTwoMetric.CM.Construction.twoFormPairedContribution f g u v =
      4 * (star (HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient f u v) * HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient g u v) := by
  rw [ComplexMultiplication.HodgeComparison.MixedTwoMetric.CM.Construction.twoFormPairedContribution, HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient_type20 f hf,
    HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient_apply]
  simp only [HolomorphicTwoCoefficient.Closedness.twoFormBilinear_type20_J f hf, HolomorphicTwoCoefficient.Closedness.twoFormBilinear_type20_J_left f hf,
    HolomorphicTwoCoefficient.Closedness.twoFormBilinear_type20_J_right f hf, star_mul, star_neg,
    Complex.star_def, Complex.conj_I]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem holomorphicTwoCoefficient_pullback (f : Analysis.DifferentialForms.Manifold.Basic.FormValue F 2) (T : E →L[ℂ] F) (u v : E) :
    HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (f.compContinuousLinearMap (T.restrictScalars ℝ)) u v =
      HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient f (T u) (T v) := by
  simp only [HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient_apply, ComplexMultiplication.HodgeComparison.MixedTwoChartMetric.CM.Construction.twoFormBilinear_pullback, map_smul]

theorem type20_pullback (f : Analysis.DifferentialForms.Manifold.Basic.FormValue F 2) (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree F 2 0 f) (T : E →L[ℂ] F) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 (f.compContinuousLinearMap (T.restrictScalars ℝ)) := by
  intro z v
  change f (fun i => T ((z : ℂ) • v i)) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 2 0 z * f (fun i => T (v i))
  simp only [map_smul]
  exact hf z (fun i => T (v i))

end Coefficients

section Metric

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
theorem formMetricPair_type20_basis (b : OrthonormalBasis ι ℂ E) (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 f) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 2 f g =
      2 * ∑ i, ∑ j, star (HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient f (b i) (b j)) *
        HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient g (b i) (b j) := by
  have h := ComplexMultiplication.HodgeComparison.MixedTwoMetric.CM.Construction.formMetricPair_two_paired_basis b f g
  simp only [holomorphicTwoCoefficient_pair f g hf, ← Finset.mul_sum] at h
  linear_combination (norm := ring_nf) -h / 2

theorem bilinear_pair_inverse_gram (b : Module.Basis ι ℂ E)
    (c : OrthonormalBasis κ ℂ E) (f g : E →ₗ[ℂ] E →ₗ[ℂ] ℂ) :
    (∑ u, ∑ v, star (f (c u) (c v)) * g (c u) (c v)) =
      ∑ j, ∑ k, ∑ d, ∑ a, star (f (b a) (b k)) * (Matrix.gram ℂ b)⁻¹ d a *
        (Matrix.gram ℂ b)⁻¹ j k * g (b d) (b j) := by
  simp_rw [ComplexMultiplication.HodgeComparison.SesquilinearMetric.CM.Construction.complex_covector_pair_inverse_gram b c]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = (Matrix.gram ℂ b)⁻¹ j k * ∑ u, star (f (c u) (b k)) * g (c u) (b j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = (Matrix.gram ℂ b)⁻¹ j k * ∑ d, ∑ a,
        star (f (b a) (b k)) * (Matrix.gram ℂ b)⁻¹ d a * g (b d) (b j) := by
      congr 1
      exact ComplexMultiplication.HodgeComparison.SesquilinearMetric.CM.Construction.complex_covector_pair_inverse_gram b c (f.flip (b k)) (g.flip (b j))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem formMetricPair_type20_inverse_gram (b : Module.Basis ι ℂ E) (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 f) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 2 f g =
      2 * ∑ j, ∑ k, ∑ d, ∑ a, star (HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient f (b a) (b k)) *
        (Matrix.gram ℂ b)⁻¹ d a * (Matrix.gram ℂ b)⁻¹ j k *
          HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient g (b d) (b j) := by
  let : FiniteDimensional ℂ E := b.finiteDimensional_of_finite
  let c := stdOrthonormalBasis ℂ E
  rw [formMetricPair_type20_basis c f g hf]
  congr 1
  exact bilinear_pair_inverse_gram b c (HolomorphicTwoCoefficient.Closedness.holomorphicTwoBilinear f) (HolomorphicTwoCoefficient.Closedness.holomorphicTwoBilinear g)

end Metric

theorem projectiveChartPair_type20_inverse_metric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V.analyticModel) (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 2 0 f) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy 2 f g =
      2 * ∑ j, ∑ k, ∑ d, ∑ a, star (HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient f (b a) (b k)) *
        (ComplexMultiplication.HodgeComparison.InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y)⁻¹ d a * (ComplexMultiplication.HodgeComparison.InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y)⁻¹ j k *
          HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient g (b d) (b j) := by
  let T := Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy
  have hG : Matrix.gram ℂ (b.map T.symm.toLinearEquiv) = ComplexMultiplication.HodgeComparison.InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y :=
    (ComplexMultiplication.HodgeComparison.HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_eq_gram V e he b hy).symm
  have htype : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) 2 0
      (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 2 f) :=
    type20_pullback f hf T.toContinuousLinearMap
  change Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 2
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 2 f)
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 2 g) = _
  rw [formMetricPair_type20_inverse_gram (b.map T.symm.toLinearEquiv) _ _ htype, hG]
  have hcoeff (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 2) (i j : ι) :
      HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 2 a)
        ((b.map T.symm.toLinearEquiv) i) ((b.map T.symm.toLinearEquiv) j) =
        HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient a (b i) (b j) := by
    change HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient
      (a.compContinuousLinearMap (T.toContinuousLinearMap.restrictScalars ℝ))
      (T.symm (b i)) (T.symm (b j)) = _
    rw [holomorphicTwoCoefficient_pullback]
    simp only [ContinuousLinearEquiv.coe_coe, T.apply_symm_apply]
  simp only [hcoeff]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoMetric.Closedness
