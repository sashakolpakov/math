import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianCoefficientSmooth
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicTestDifferential
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts

/-! # Holomorphic Adjoint Flux -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicAdjointFlux.CM.Construction

noncomputable section

section

/-! Smooth fixed-coordinate fluxes for the actual adjoint on holomorphic
one-forms. The coordinate formulas use the genuine metric and volume. -/

open _root_.MeasureTheory
open scoped ContDiff SchwartzMap

def varietyOneFormComplexCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (k : Fin V.complexDimension) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  a.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) (fun _ => HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V k)

theorem varietyOneFormComplexCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (k : Fin V.complexDimension) :
    ContDiffOn ℝ ∞ (varietyOneFormComplexCoefficient V e a k)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) := by
  have hraw : ContDiffOn ℝ ∞ (a.val.inChart e) e.target := by
    simpa only [Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, Set.preimage_univ, Set.inter_univ] using a.smooth e he
  have hv := Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.smooth_fixed_form_evaluation 1
    (fun _ => HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V k) hraw
  exact hv.comp ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ).contDiffOn
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates_mapsTo V e)

def varietyHolomorphicAdjointFlux (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (j : Fin V.complexDimension) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  ∑ k, star (varietyOneFormComplexCoefficient V e a k z) * HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse V e z j k

theorem varietyHolomorphicAdjointFlux_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (j : Fin V.complexDimension) :
    ContDiffOn ℝ ∞ (varietyHolomorphicAdjointFlux V e a j)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) := by
  apply ContDiffOn.sum
  intro k _
  exact (Complex.conjCLE.contDiff.comp_contDiffOn
    (varietyOneFormComplexCoefficient_smooth V e he a k)).mul
    (HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse_smooth V e he j k)

theorem holomorphicDirectionalDerivative_zero_off_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    (g : E → ℂ) {x : E} (hx : x ∉ tsupport g) (u : E) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g x u = 0 := by
  have hD : fderiv ℝ g x = 0 := by
    rw [(notMem_tsupport_iff_eventuallyEq.mp hx).fderiv_eq]
    exact fderiv_const_apply 0
  rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, hD]
  simp only [zero_apply, mul_zero, sub_zero]

theorem projectiveL2Pair_holomorphic_flux_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 a
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg)) =
      2 * ∫ z, ∑ j, varietyHolomorphicAdjointFlux V e a j z *
        MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) := by
  rw [HolomorphicTestDifferential.CM.Construction.projectiveL2Pair_holomorphic_chart_test V e he a ha g hgc hg]
  have hi (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
      (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
        (2 * ∑ j, ∑ k, star (varietyOneFormComplexCoefficient V e a k z) *
          (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹ j k *
          MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)) =
      2 * ∑ j, varietyHolomorphicAdjointFlux V e a j z *
        MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) := by
    simp only [varietyHolomorphicAdjointFlux, HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  change (∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
    (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * (2 * ∑ j, ∑ k,
      star (varietyOneFormComplexCoefficient V e a k z) *
        (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹ j k *
        MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j))) = _
  simp_rw [hi]
  rw [integral_const_mul]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  apply Finset.sum_eq_zero
  intro j _
  rw [holomorphicDirectionalDerivative_zero_off_support g (fun h => hz (hg h)), mul_zero]

end

/-! Integration of the actual holomorphic one-form flux against compact
tests gives its coordinate divergence, with no boundary term. -/

open _root_.MeasureTheory
open scoped ContDiff SchwartzMap

section Integrability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] in
theorem holomorphic_test_product_integrable (w g : E → ℂ) {U : Set E}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hs : tsupport g ⊆ U) (u : E) :
    Integrable (fun x => w x * MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g x u) μ := by
  have hL (v : E) := HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable μ w _ hU hw
    (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative g hg v) (hgc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hs)
  convert ((hL u).sub ((hL (Complex.I • u)).const_mul Complex.I)).const_mul (1 / 2 : ℂ) using 1
  funext x
  rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative]
  simp only [Pi.sub_apply]
  ring

omit [FiniteDimensional ℝ E] in
theorem holomorphic_flux_product_integrable (w g : E → ℂ) {U : Set E}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hs : tsupport g ⊆ U) (u : E) :
    Integrable (fun x => MetricDerivative.CM.Construction.holomorphicDirectionalDerivative w x u * g x) μ := by
  have hR (v : E) := HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable μ _ g hU
    (Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smoothOn_directional_derivative w hU hw v) hg hgc hs
  convert ((hR u).sub ((hR (Complex.I • u)).const_mul Complex.I)).const_mul (1 / 2 : ℂ) using 1
  funext x
  rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative]
  simp only [Pi.sub_apply]
  ring

end Integrability

def varietyHolomorphicFluxDivergence (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  ∑ j, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (varietyHolomorphicAdjointFlux V e a j) z
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)

theorem projectiveL2Pair_holomorphic_flux_divergence (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 a
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg)) =
      -(2 * ∫ z, varietyHolomorphicFluxDivergence V e a z * g z) := by
  have hL (j : Fin V.complexDimension) := holomorphic_test_product_integrable volume
    (varietyHolomorphicAdjointFlux V e a j) g (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (varietyHolomorphicAdjointFlux_smooth V e he a j) (g.smooth ⊤) hgc hg
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)
  have hR (j : Fin V.complexDimension) := holomorphic_flux_product_integrable volume
    (varietyHolomorphicAdjointFlux V e a j) g (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (varietyHolomorphicAdjointFlux_smooth V e he a j) (g.smooth ⊤) hgc hg
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)
  rw [projectiveL2Pair_holomorphic_flux_test V e he a ha g hgc hg,
    integral_finsetSum _ (fun j _ => hL j)]
  have hi (j : Fin V.complexDimension) := HolomorphicIntegrationByParts.CM.Construction.integral_mul_holomorphicDirectionalDerivative_on volume
    (varietyHolomorphicAdjointFlux V e a j) g (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (varietyHolomorphicAdjointFlux_smooth V e he a j) (g.smooth ⊤) hgc hg
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)
  simp_rw [hi]
  simp only [varietyHolomorphicFluxDivergence, Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => hR j), Finset.sum_neg_distrib, mul_neg]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicAdjointFlux.CM.Construction
