import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoMetric
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SesquilinearMetric

/-! # Mixed Two Chart Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoChartMetric.CM.Construction

noncomputable section

/-! The actual projective two-form metric in fixed complex coordinates,
with both inverse-Hermitian factors and the exact factor four. -/

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

theorem twoFormBilinear_pullback (f : Analysis.DifferentialForms.Manifold.Basic.FormValue F 2) (T : E →L[ℂ] F) (u v : E) :
    KahlerDifferential.CM.Construction.twoFormBilinear (f.compContinuousLinearMap (T.restrictScalars ℝ)) u v =
      KahlerDifferential.CM.Construction.twoFormBilinear f (T u) (T v) := by
  rw [KahlerDifferential.CM.Construction.twoFormBilinear_apply, KahlerDifferential.CM.Construction.twoFormBilinear_apply]
  change f (fun j => T (![u, v] j)) = f ![T u, T v]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem mixedTwoCoefficient_pullback (f : Analysis.DifferentialForms.Manifold.Basic.FormValue F 2) (T : E →L[ℂ] F) (u v : E) :
    MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (f.compContinuousLinearMap (T.restrictScalars ℝ)) u v =
      MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient f (T u) (T v) := by
  simp only [MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient_apply, twoFormBilinear_pullback, map_smul]

theorem type11_pullback (f : Analysis.DifferentialForms.Manifold.Basic.FormValue F 2) (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree F 1 1 f) (T : E →L[ℂ] F) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 (f.compContinuousLinearMap (T.restrictScalars ℝ)) := by
  intro z v
  change f (fun i => T ((z : ℂ) • v i)) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 z * f (fun i => T (v i))
  simp only [map_smul]
  exact hf z (fun i => T (v i))

end

section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι]

theorem formMetricPair_type11_inverse_gram (b : Module.Basis ι ℂ E) (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 f) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 2 f g =
      4 * ∑ j, ∑ k, ∑ a, ∑ d, star (MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient f (b a) (b k)) *
        (Matrix.gram ℂ b)⁻¹ a d * (Matrix.gram ℂ b)⁻¹ j k * MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient g (b d) (b j) := by
  let : FiniteDimensional ℂ E := b.finiteDimensional_of_finite
  let c := stdOrthonormalBasis ℂ E
  rw [MixedTwoMetric.CM.Construction.formMetricPair_type11_basis c f g hf]
  congr 1
  exact SesquilinearMetric.CM.Construction.sesquilinear_pair_inverse_gram b c (MixedTwoCoefficient.CM.Construction.mixedTwoSesquilinear f) (MixedTwoCoefficient.CM.Construction.mixedTwoSesquilinear g)

end

theorem projectiveChartPair_type11_inverse_metric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V.analyticModel) (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 1 f) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy 2 f g =
      4 * ∑ j, ∑ k, ∑ a, ∑ d, star (MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient f (b a) (b k)) *
        (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y)⁻¹ a d * (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y)⁻¹ j k *
          MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient g (b d) (b j) := by
  let T := Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy
  have hG : Matrix.gram ℂ (b.map T.symm.toLinearEquiv) = InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y :=
    (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_eq_gram V e he b hy).symm
  have htype : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) 1 1
      (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 2 f) :=
    type11_pullback f hf T.toContinuousLinearMap
  change Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 2 (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 2 f)
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 2 g) = _
  rw [formMetricPair_type11_inverse_gram (b.map T.symm.toLinearEquiv) _ _ htype, hG]
  have hcoeff (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 2) (i j : ι) :
      MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 2 a)
        ((b.map T.symm.toLinearEquiv) i) ((b.map T.symm.toLinearEquiv) j) =
        MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient a (b i) (b j) := by
    change MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (a.compContinuousLinearMap (T.toContinuousLinearMap.restrictScalars ℝ))
      (T.symm (b i)) (T.symm (b j)) = _
    rw [mixedTwoCoefficient_pullback]
    simp only [ContinuousLinearEquiv.coe_coe, T.apply_symm_apply]
  simp only [hcoeff]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoChartMetric.CM.Construction
