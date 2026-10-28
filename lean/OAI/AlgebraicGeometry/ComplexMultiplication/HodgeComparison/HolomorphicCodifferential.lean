import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicAdjointFlux
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ScalarTestPairing
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth

/-! # Holomorphic Codifferential -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicCodifferential.CM.Construction

noncomputable section

section

/-! The actual global codifferential of a holomorphic one-form equals its
local flux divergence. The formula follows from the genuine global adjoint
identity and compact test separation. -/

open _root_.MeasureTheory Set
open scoped ContDiff SchwartzMap

theorem varietyHolomorphicFluxDivergence_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    ContDiffOn ℝ ∞ (HolomorphicAdjointFlux.CM.Construction.varietyHolomorphicFluxDivergence V e a)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) := by
  apply ContDiffOn.sum
  intro j _
  have hD (u : EuclideanMetric.CM.Construction.varietyEuclideanModel V) := Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smoothOn_directional_derivative
    (HolomorphicAdjointFlux.CM.Construction.varietyHolomorphicAdjointFlux V e a j) (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (HolomorphicAdjointFlux.CM.Construction.varietyHolomorphicAdjointFlux_smooth V e he a j) u
  exact contDiffOn_const.mul ((hD _).sub (contDiffOn_const.mul (hD _)))

def varietyWeightedCodifferentialCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
    star (ScalarChartLocalization.CM.Construction.varietyScalarChart V e (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a) z)

theorem varietyWeightedCodifferentialCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    ContDiffOn ℝ ∞ (varietyWeightedCodifferentialCoefficient V e a)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn (Metric.CM.Construction.varietyMetricDensity_smooth V e he)).mul
    (Complex.conjCLE.contDiff.comp_contDiffOn
      (ScalarChartLocalization.CM.Construction.varietyScalarChart_smooth V e he (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a)))

theorem varietyHolomorphicCodifferential_flux_identity (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    varietyWeightedCodifferentialCoefficient V e a z +
      2 * HolomorphicAdjointFlux.CM.Construction.varietyHolomorphicFluxDivergence V e a z = 0 := by
  let Q := varietyWeightedCodifferentialCoefficient V e a
  let D := HolomorphicAdjointFlux.CM.Construction.varietyHolomorphicFluxDivergence V e a
  let R := fun w => Q w + 2 * D w
  have hQ := varietyWeightedCodifferentialCoefficient_smooth V e he a
  have hD := varietyHolomorphicFluxDivergence_smooth V e he a
  have hR : ContDiffOn ℝ ∞ R (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
    hQ.add (contDiffOn_const.mul hD)
  have hzero : EqOn R 0 (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) := by
    apply Smooth.CM.Construction.continuous_zero_of_schwartz_tests (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen R hR.continuousOn
    intro g hgc hg
    have hQg := HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable volume Q g (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hQ
      (g.smooth ⊤) hgc hg
    have hDg := HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable volume D g (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hD
      (g.smooth ⊤) hgc hg
    have hp := Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential_pair V 0 (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg) a
    rw [HolomorphicAdjointFlux.CM.Construction.projectiveL2Pair_holomorphic_flux_divergence V e he a ha g hgc hg,
      ScalarTestPairing.CM.Construction.projectiveL2Pair_zero_chart_test V e he (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a) g hgc hg] at hp
    change -(2 * ∫ w, D w * g w) =
      ∫ w in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)), Q w * g w at hp
    have hoff : ∀ w, w ∉ (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) → Q w * g w = 0 := by
      intro w hw
      have hgzero : g w = 0 := image_eq_zero_of_notMem_tsupport (fun h => hw (hg h))
      rw [hgzero, mul_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hoff] at hp
    have hr : (fun w => R w * g w) = (fun w => Q w * g w + 2 * (D w * g w)) := by
      funext w
      dsimp only [R]
      ring
    rw [hr, integral_add hQg (hDg.const_mul 2), integral_const_mul, ← hp]
    ring
  exact hzero hz

end

section

/-! Kähler coefficient divergence removes the metric-derivative terms
from the actual holomorphic one-form adjoint flux. -/

theorem holomorphicDirectionalDerivative_sum {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [Fintype ι]
    (f : ι → E → ℂ) {x : E} (hf : ∀ i, DifferentiableAt ℝ (f i) x) (u : E) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => ∑ i, f i y) x u =
      ∑ i, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (f i) x u := by
  simp only [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative]
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp only [sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]

theorem varietyHolomorphicFluxDivergence_cancel (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    HolomorphicAdjointFlux.CM.Construction.varietyHolomorphicFluxDivergence V e a z =
      ∑ j, ∑ k, HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse V e z j k *
        MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun w => star (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a k w)) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) := by
  have hA (k : Fin V.complexDimension) :=
    ((HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient_smooth V e he a k).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hP (j k : Fin V.complexDimension) :=
    ((HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse_smooth V e he j k).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hzero (k : Fin V.complexDimension) :
      (∑ j, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun w => HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse V e w j k) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)) = 0 :=
    MetricCoefficientDivergence.CM.Construction.varietyEuclideanMetric_weighted_inverse_divergence V e he hz k
  have hflux (j : Fin V.complexDimension) :
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (HolomorphicAdjointFlux.CM.Construction.varietyHolomorphicAdjointFlux V e a j) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) =
      ∑ k, (star (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a k z) *
        MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun w => HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse V e w j k) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) +
        HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse V e z j k *
          MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun w => star (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a k w)) z
            (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)) := by
    change MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
      (fun w => ∑ k, star (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a k w) *
        HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse V e w j k) z
      (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) = _
    refine (holomorphicDirectionalDerivative_sum
      (fun k w => star (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a k w) *
        HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse V e w j k)
      (fun k => (hA k).star.mul (hP j k)) _).trans ?_
    apply Finset.sum_congr rfl
    intro k _
    exact HolomorphicMatrixCalculus.CM.Construction.holomorphicDirectionalDerivative_mul _ _ (hA k).star (hP j k) _
  rw [HolomorphicAdjointFlux.CM.Construction.varietyHolomorphicFluxDivergence]
  simp_rw [hflux, Finset.sum_add_distrib]
  have hcancel : (∑ j, ∑ k, star (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a k z) *
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun w => HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse V e w j k) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    rw [← Finset.mul_sum, hzero, mul_zero]
  rw [hcancel, zero_add]

end

/-! In complex coordinates the genuine codifferential of a pure (1,0)
one-form is minus twice the inverse-Hermitian contraction of its
antiholomorphic coefficient derivatives. -/

open scoped ComplexOrder

theorem holomorphicDirectionalDerivative_star {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    (f : E → ℂ) (x u : E) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => star (f y)) x u =
      star (AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative f x u) := by
  have hD (v : E) : fderiv ℝ (fun y => star (f y)) x v = star (fderiv ℝ f x v) := by
    exact congrArg (fun L : E →L[ℝ] ℂ => L v) (fderiv_star (𝕜 := ℝ) (f := f) (x := x))
  rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative, hD, hD]
  simp only [star_mul, star_add, star_div₀, star_one, star_ofNat, Complex.star_def, Complex.conj_I]
  ring

def varietyHolomorphicAdjointContraction (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  ∑ j, ∑ k, (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹ k j *
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a k) z
      (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)

theorem varietyHolomorphicFluxDivergence_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    star (HolomorphicAdjointFlux.CM.Construction.varietyHolomorphicFluxDivergence V e a z) =
      (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * varietyHolomorphicAdjointContraction V e a z := by
  rw [varietyHolomorphicFluxDivergence_cancel V e he a hz]
  simp only [star_sum, varietyHolomorphicAdjointContraction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [holomorphicDirectionalDerivative_star, star_mul, star_star]
  have hP := (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_posDef V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hz).isHermitian.inv.apply k j
  have hW : star (HermitianCoefficientSmooth.CM.Construction.varietyWeightedHermitianInverse V e z j k) =
      (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
        (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹ k j := by
    change star ((Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * _) = _
    rw [star_mul, show star (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) = (Metric.CM.Construction.varietyMetricDensity V e z : ℂ)
      from Complex.conj_ofReal _, hP, mul_comm]
  rw [hW]
  ring

theorem varietyHolomorphicCodifferential_formula (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ScalarChartLocalization.CM.Construction.varietyScalarChart V e (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a) z =
      -2 * varietyHolomorphicAdjointContraction V e a z := by
  have h := congrArg (star : ℂ → ℂ) (varietyHolomorphicCodifferential_flux_identity V e he a ha hz)
  rw [star_add, star_mul, star_ofNat, star_zero, varietyHolomorphicFluxDivergence_conjugate V e he a hz] at h
  have hQ : star (varietyWeightedCodifferentialCoefficient V e a z) =
      (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
        ScalarChartLocalization.CM.Construction.varietyScalarChart V e (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a) z := by
    rw [varietyWeightedCodifferentialCoefficient, star_mul, star_star,
      show star (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) = (Metric.CM.Construction.varietyMetricDensity V e z : ℂ)
        from Complex.conj_ofReal _, mul_comm]
  rw [hQ] at h
  have hρ : (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Metric.CM.Construction.varietyMetricDensity_pos V e he hz).ne'
  apply (mul_left_cancel₀ hρ)
  linear_combination h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicCodifferential.CM.Construction
