import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveInverseTransport
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormFluxAlgebra
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace

/-! # Antiholomorphic Integration -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction

noncomputable section

section

/-! Closed projective (1,1) forms with zero Hermitian trace have
divergence-free adjoint flux in the actual metric and volume density. -/

open Filter
open scoped ContDiff _root_.Topology ComplexOrder

def varietyInverseHermitianMatrix (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Matrix (Fin V.complexDimension) (Fin V.complexDimension) ℂ :=
  (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹

def varietyConjugateTwoMatrix (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Matrix (Fin V.complexDimension) (Fin V.complexDimension) ℂ :=
  Matrix.of fun i j => star (TwoFormChartCoefficients.CM.Construction.varietyTwoFormMixedCoefficient V e a i j z)

def varietyMixedTwoAdjointFlux (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (j d : Fin V.complexDimension) :
    EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  TwoFormFluxAlgebra.CM.Construction.raisedTwoFlux (fun z => (Metric.CM.Construction.varietyMetricDensity V e z : ℂ))
    (varietyInverseHermitianMatrix V e) (varietyConjugateTwoMatrix V e a) j d

theorem varietyInverseHermitianMatrix_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (i j : Fin V.complexDimension) :
    ContDiffOn ℝ ∞ (fun z => varietyInverseHermitianMatrix V e z i j)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  (HermitianCoefficientSmooth.CM.Construction.varietyHermitianMatrix_inverse_smooth V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) i j).comp
    ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ).contDiffOn
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates_mapsTo V e)

theorem varietyConjugateTwoMatrix_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (i j : Fin V.complexDimension) :
    ContDiffOn ℝ ∞ (fun z => varietyConjugateTwoMatrix V e a z i j)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  Complex.conjCLE.contDiff.comp_contDiffOn (TwoFormChartCoefficients.CM.Construction.varietyTwoFormMixedCoefficient_smooth V e he a i j)

theorem varietyMixedTwoAdjointFlux_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (j d : Fin V.complexDimension) :
    ContDiffOn ℝ ∞ (varietyMixedTwoAdjointFlux V e a j d) (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  unfold varietyMixedTwoAdjointFlux TwoFormFluxAlgebra.CM.Construction.raisedTwoFlux
  apply ContDiffOn.sum
  intro r _
  apply ContDiffOn.sum
  intro k _
  exact (((Complex.ofRealCLM.contDiff.comp_contDiffOn (Metric.CM.Construction.varietyMetricDensity_smooth V e he)).mul
    (varietyInverseHermitianMatrix_smooth V e he r d)).mul
      (varietyInverseHermitianMatrix_smooth V e he j k)).mul
        (varietyConjugateTwoMatrix_smooth V e he a r k)

theorem variety_raised_two_trace_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    TwoFormFluxAlgebra.CM.Construction.raisedTwoTrace (varietyInverseHermitianMatrix V e) (varietyConjugateTwoMatrix V e a) z =
      star (HolomorphicExteriorTrace.CM.Construction.varietyTwoFormTrace V e a z) := by
  simp only [TwoFormFluxAlgebra.CM.Construction.raisedTwoTrace, HolomorphicExteriorTrace.CM.Construction.varietyTwoFormTrace, star_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hP := (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_posDef V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hz).isHermitian.inv.apply j k
  change _ = star (_ * TwoFormChartCoefficients.CM.Construction.varietyTwoFormMixedCoefficient V e a j k z)
  rw [star_mul, hP]
  exact mul_comm _ _

theorem variety_closed_two_conjugate_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 a.val)
    (hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (d r k : Fin V.complexDimension) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => varietyConjugateTwoMatrix V e a y r k) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d) =
      AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => varietyConjugateTwoMatrix V e a y r d) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ k) := by
  change AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => star (TwoFormChartCoefficients.CM.Construction.varietyTwoFormMixedCoefficient V e a r k y)) z _ =
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => star (TwoFormChartCoefficients.CM.Construction.varietyTwoFormMixedCoefficient V e a r d y)) z _
  rw [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_star, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_star]
  exact congrArg (star : ℂ → ℂ) (TwoFormChartCoefficients.CM.Construction.variety_closed_type11_holomorphic_derivative V e he a ha hc hz d r k)

theorem variety_closed_trace_zero_two_flux_divergence (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 a.val)
    (hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    (ht : ∀ z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, HolomorphicExteriorTrace.CM.Construction.varietyTwoFormTrace V e a z = 0)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (j : Fin V.complexDimension) :
    (∑ d, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (varietyMixedTwoAdjointFlux V e a j d) z
      (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)) = 0 := by
  let P := varietyInverseHermitianMatrix V e
  let S := varietyConjugateTwoMatrix V e a
  let ρ := fun y => (Metric.CM.Construction.varietyMetricDensity V e y : ℂ)
  have hρ : DifferentiableAt ℝ ρ z :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (Metric.CM.Construction.varietyMetricDensity_smooth V e he)).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hP (r k : Fin V.complexDimension) : DifferentiableAt ℝ (fun y => P y r k) z :=
    ((varietyInverseHermitianMatrix_smooth V e he r k).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hS (r k : Fin V.complexDimension) : DifferentiableAt ℝ (fun y => S y r k) z :=
    ((varietyConjugateTwoMatrix_smooth V e he a r k).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hzero : TwoFormFluxAlgebra.CM.Construction.raisedTwoTrace P S =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    exact (variety_raised_two_trace_conjugate V e he a hy).trans (by rw [ht y hy, star_zero])
  have hd (d : Fin V.complexDimension) : AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (TwoFormFluxAlgebra.CM.Construction.raisedTwoTrace P S) z
      (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d) = 0 := by
    rw [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_congr hzero]
    simp only [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative, fderiv_const_apply, zero_apply, mul_zero, add_zero]
  have h := TwoFormFluxAlgebra.CM.Construction.raisedTwoFlux_divergence_trace ρ P S hρ hP hS
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ)
    (AntiholomorphicDivergence.CM.Construction.varietyEuclideanMetric_weighted_inverse_antiholomorphic_divergence V e he hz)
    (ProjectiveInverseTransport.CM.Construction.varietyEuclideanInverse_antiholomorphic_transport V e he hz)
    (variety_closed_two_conjugate_derivative V e he a ha hc hz) j
  exact h.trans (by simp only [hd, mul_zero, Finset.sum_const_zero])

end

/-! Antiholomorphic integration by parts and the vanishing of a
divergence-free flux against compactly supported scalar derivatives. -/

open _root_.MeasureTheory
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

theorem antiholomorphicDirectionalDerivative_smoothOn (w : E → ℂ) {U : Set E} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) (u : E) :
    ContDiffOn ℝ ∞ (fun x => AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative w x u) U := by
  exact contDiffOn_const.mul
    ((Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smoothOn_directional_derivative w hU hw u).add
      (contDiffOn_const.mul (Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smoothOn_directional_derivative w hU hw (Complex.I • u))))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem integral_mul_antiholomorphicDirectionalDerivative_on (w g : E → ℂ) {U : Set E}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hs : tsupport g ⊆ U) (u : E) :
    (∫ x, w x * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative g x u ∂μ) =
      -(∫ x, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative w x u * g x ∂μ) := by
  have hL (v : E) := HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable μ w _ hU hw
    (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative g hg v) (hgc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hs)
  have hR (v : E) := HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable μ _ g hU
    (Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smoothOn_directional_derivative w hU hw v) hg hgc hs
  have hLf (x : E) : w x * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative g x u =
      (1 / 2 : ℂ) * (w x * fderiv ℝ g x u + Complex.I * (w x * fderiv ℝ g x (Complex.I • u))) := by
    rw [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative]
    ring
  have hRf (x : E) : AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative w x u * g x =
      (1 / 2 : ℂ) * (fderiv ℝ w x u * g x + Complex.I * (fderiv ℝ w x (Complex.I • u) * g x)) := by
    rw [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative]
    ring
  simp_rw [hLf, hRf]
  rw [integral_const_mul, integral_const_mul,
    integral_add (hL u) ((hL (Complex.I • u)).const_mul Complex.I), integral_const_mul,
    integral_add (hR u) ((hR (Complex.I • u)).const_mul Complex.I), integral_const_mul,
    HolomorphicIntegrationByParts.CM.Construction.integral_mul_directional_on μ w g hU hw hg hgc hs u,
    HolomorphicIntegrationByParts.CM.Construction.integral_mul_directional_on μ w g hU hw hg hgc hs (Complex.I • u)]
  ring

omit [FiniteDimensional ℝ E] in
theorem antiholomorphic_test_product_integrable (w g : E → ℂ) {U : Set E}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hs : tsupport g ⊆ U) (u : E) :
    Integrable (fun x => w x * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative g x u) μ := by
  have h (v : E) := HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable μ w _ hU hw
    (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative g hg v) (hgc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hs)
  convert ((h u).add ((h (Complex.I • u)).const_mul Complex.I)).const_mul (1 / 2 : ℂ) using 1
  funext x
  change w x * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative g x u =
    (1 / 2 : ℂ) * (w x * fderiv ℝ g x u + Complex.I * (w x * fderiv ℝ g x (Complex.I • u)))
  rw [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative]
  ring

theorem integral_divergence_free_antiholomorphic_flux {ι : Type*} [Fintype ι]
    (w : ι → E → ℂ) (v : ι → E) (g : E → ℂ) {U : Set E} (hU : IsOpen U)
    (hw : ∀ i, ContDiffOn ℝ ∞ (w i) U) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hs : tsupport g ⊆ U)
    (hdiv : ∀ x ∈ U, (∑ i, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (w i) x (v i)) = 0) :
    (∫ x, ∑ i, w i x * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative g x (v i) ∂μ) = 0 := by
  have hL (i : ι) := antiholomorphic_test_product_integrable μ (w i) g hU (hw i) hg hgc hs (v i)
  have hR (i : ι) := HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable μ _ g hU
    (antiholomorphicDirectionalDerivative_smoothOn (w i) hU (hw i) (v i)) hg hgc hs
  have hzero (x : E) : (∑ i, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (w i) x (v i) * g x) = 0 := by
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ U
    · rw [hdiv x hx, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero]
  rw [integral_finsetSum _ (fun i _ => hL i)]
  simp_rw [integral_mul_antiholomorphicDirectionalDerivative_on μ _ g hU (hw _) hg hgc hs]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hR i)]
  simp only [hzero, integral_zero, neg_zero]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction
