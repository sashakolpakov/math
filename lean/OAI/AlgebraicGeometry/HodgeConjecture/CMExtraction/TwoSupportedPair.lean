import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveTwoFlux
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoExterior
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoDensity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormSupportedPair

/-! # Two Supported Pair -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoSupportedPair.Closedness

noncomputable section

/-! The genuine projective pairing against a supported derivative is the (2,0) flux integral. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormSupportedPair.CM.Construction _root_.MeasureTheory
open scoped ComplexOrder

theorem tsupport_conjugate {X : Type*} [TopologicalSpace X] (f : X → ℂ) :
    tsupport (fun x => star (f x)) = tsupport f := by
  apply congrArg closure
  ext x
  simp only [Function.mem_support, ne_eq, star_eq_zero]

theorem projectiveL2Pair_type20_supported_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 2 0 a.val)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (hb : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 b.val)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (hs : ∀ x, x ∉ K → b x = 0) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 2 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) a =
      4 * ∫ z, ∑ j, ∑ d, ProjectiveTwoFlux.Closedness.varietyHolomorphicTwoFlux V e a j d z *
        ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => star (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j y)) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d) := by
  let c := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b
  have hc : ∀ x, x ∉ e.source → c x = 0 := by
    intro x hx
    exact Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.manifold_d_zero_off_closed V 1 b hK.isClosed hs (fun h => hx (hKe h))
  have hpzero (x : V.analyticSpace) (hx : x ∉ e.source) :
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 2 c.val a.val x = 0 := by
    rw [← Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm,
      Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_zero_of_right V 2 a.val c.val x (hc x hx), star_zero]
  rw [Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair,
    Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 2 c.val a.val)
    (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveFormPointPair_continuous V 2 c a).aestronglyMeasurable hpzero]
  have hchart (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
      (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
        Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 2 c.val a.val
          (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) =
      4 * ∑ j, ∑ d, ProjectiveTwoFlux.Closedness.varietyHolomorphicTwoFlux V e a j d z *
        ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => star (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j y)) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d) := by
    have hzy : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z ∈ e.target := hz
    have hp : Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 2 a.val c.val
        (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) =
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hzy 2
        (a.val.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
        (c.val.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
      simpa only [e.right_inv hzy, Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse] using
        Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he _ (e.map_target hzy) 2 a.val c.val
    rw [← Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm, hp,
      TwoMetric.Closedness.projectiveChartPair_type20_inverse_metric V e he _ hzy (ComplexMultiplication.HodgeComparison.HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
        _ _ (ha e he _ hzy)]
    have hP (i j : Fin V.complexDimension) :=
      (ComplexMultiplication.HodgeComparison.HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_posDef V e he (ComplexMultiplication.HodgeComparison.HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hzy).isHermitian.inv.apply i j
    simp only [star_mul, star_ofNat, star_sum, star_star, hP]
    rw [mul_comm _ (2 : ℂ)]
    let D : Matrix (Fin V.complexDimension) (Fin V.complexDimension) ℂ :=
      Matrix.of fun d j => ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative
        (fun y => star (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j y)) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)
    have hcoef (d j : Fin V.complexDimension) :
        star (HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (c.val.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
          (ComplexMultiplication.HodgeComparison.HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V d) (ComplexMultiplication.HodgeComparison.HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V j)) = D d j - D j d := by
      have hd := TwoExterior.Closedness.variety_type10_exterior_holomorphic_coefficient V e he b hb hz d j
      have hj (r t : Fin V.complexDimension) :
          star (ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (ComplexMultiplication.HodgeComparison.HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e b t) z
            (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ r)) = D r t := by
        change _ = ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => star
          (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b t y)) z _
        rw [ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_star,
          ComplexMultiplication.HodgeComparison.MetricCoefficientDivergence.CM.Construction.holomorphicDirectionalDerivative_congr
            (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient_eventuallyEq V e b t hz)]
      exact (congrArg star hd).trans (by rw [star_sub, hj, hj])
    calc
      _ = (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * (2 * ∑ j, ∑ k, ∑ d, ∑ r,
          ProjectiveTwoFlux.Closedness.varietyHolomorphicTwoMatrix V e a z r k * ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction.varietyInverseHermitianMatrix V e z r d *
            ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction.varietyInverseHermitianMatrix V e z k j * (D d j - D j d)) := by
        congr 2
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro r _
        exact (congrArg (· * _) (hcoef d j)).trans (by
          dsimp only [ProjectiveTwoFlux.Closedness.varietyHolomorphicTwoMatrix, ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction.varietyInverseHermitianMatrix,
            TwoChart.Closedness.varietyHolomorphicTwoCoefficient, Matrix.of_apply]
          ring)
      _ = _ := TwoDensity.Closedness.holomorphic_two_density_flux _ _ _ D (fun r k => HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient_skew _ _ _)
  calc
    _ = ∫ z in (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _),
        4 * ∑ j, ∑ d, ProjectiveTwoFlux.Closedness.varietyHolomorphicTwoFlux V e a j d z *
          ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => star (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j y)) z
            (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d) :=
      setIntegral_congr_fun (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet hchart
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro d _
      have hn : z ∉ tsupport (fun y => star (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j y)) := by
        rw [tsupport_conjugate]
        exact fun h => hz (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient_tsupport_domain V e b j hK hKe hs h)
      rw [ComplexMultiplication.HodgeComparison.TwoFormSupportedPair.CM.Construction.antiholomorphicDirectionalDerivative_zero_off_support _ hn, mul_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoSupportedPair.Closedness
