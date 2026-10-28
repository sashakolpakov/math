import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace

/-! # Two Form Supported Pair -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormSupportedPair.CM.Construction

noncomputable section

/-! The actual global pairing against the exterior derivative of a
supported (1,0) one-form is its compactly supported complex flux integral. -/

open _root_.MeasureTheory

theorem mixed_two_density_flux {ι : Type*} [Fintype ι]
    (ρ : ℂ) (P S D : Matrix ι ι ℂ) :
    ρ * (4 * ∑ j, ∑ k, ∑ a, ∑ d, S a k * P a d * P j k * D d j) =
      4 * ∑ j, ∑ d, (∑ a, ∑ k, (ρ * P a d) * P j k * S a k) * D d j := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [TwoFormFluxAlgebra.CM.Construction.sum_three_reverse]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem antiholomorphicDirectionalDerivative_zero_off_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    (g : E → ℂ) {x : E} (hx : x ∉ tsupport g) (u : E) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative g x u = 0 := by
  have hD : fderiv ℝ g x = 0 := by
    rw [(notMem_tsupport_iff_eventuallyEq.mp hx).fderiv_eq]
    exact fderiv_const_apply 0
  rw [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative, hD]
  simp only [zero_apply, mul_zero, add_zero]

theorem projectiveL2Pair_type11_supported_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 a.val)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (hb : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 b.val)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (hs : ∀ x, x ∉ K → b x = 0) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 2 a (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) =
      4 * ∫ z, ∑ j, ∑ d, AntiholomorphicIntegration.CM.Construction.varietyMixedTwoAdjointFlux V e a j d z *
        AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d) := by
  let c := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b
  have hc : ∀ x, x ∉ e.source → c x = 0 := by
    intro x hx
    exact Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.manifold_d_zero_off_closed V 1 b hK.isClosed hs (fun h => hx (hKe h))
  rw [Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair, Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 2 a.val c.val)
    (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveFormPointPair_continuous V 2 a c).aestronglyMeasurable
    (fun x hx => Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_zero_of_right V 2 a.val c.val x (hc x hx))]
  have hchart (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
      (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
        Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 2 a.val c.val (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) =
      4 * ∑ j, ∑ d, AntiholomorphicIntegration.CM.Construction.varietyMixedTwoAdjointFlux V e a j d z *
        AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d) := by
    have hzy : EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z ∈ e.target := hz
    have hp : Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 2 a.val c.val
        (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) =
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hzy 2
        (a.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
        (c.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
      simpa only [e.right_inv hzy, Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse] using
        Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he _ (e.map_target hzy) 2 a.val c.val
    rw [hp, MixedTwoChartMetric.CM.Construction.projectiveChartPair_type11_inverse_metric V e he _ hzy (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
      _ _ (ha e he _ hzy)]
    have hcoef (r j : Fin V.complexDimension) :
        MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (c.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
          (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V r) (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V j) =
        AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ r) :=
      (HolomorphicExteriorTrace.CM.Construction.variety_type10_exterior_mixed_coefficient V e he b hb hz r j).trans
        (AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_congr
          (HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient_eventuallyEq V e b j hz) _).symm
    let D : Matrix (Fin V.complexDimension) (Fin V.complexDimension) ℂ :=
      Matrix.of fun d j => AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative
        (HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)
    calc
      _ = (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * (4 * ∑ j, ∑ k, ∑ r, ∑ d,
          AntiholomorphicIntegration.CM.Construction.varietyConjugateTwoMatrix V e a z r k * AntiholomorphicIntegration.CM.Construction.varietyInverseHermitianMatrix V e z r d *
            AntiholomorphicIntegration.CM.Construction.varietyInverseHermitianMatrix V e z j k * D d j) := by
        congr 2
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro d _
        exact congrArg (_ * ·) (hcoef d j)
      _ = _ := mixed_two_density_flux _ _ _ D
  calc
    _ = ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _),
        4 * ∑ j, ∑ d, AntiholomorphicIntegration.CM.Construction.varietyMixedTwoAdjointFlux V e a j d z *
          AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j) z
            (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d) :=
      setIntegral_congr_fun (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet hchart
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro d _
      rw [antiholomorphicDirectionalDerivative_zero_off_support _
        (fun h => hz (HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient_tsupport_domain V e b j hK hKe hs h)), mul_zero]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormSupportedPair.CM.Construction
