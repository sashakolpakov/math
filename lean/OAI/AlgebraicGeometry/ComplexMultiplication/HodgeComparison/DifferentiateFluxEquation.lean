import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDerivativeCoordinates
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Elliptic

/-! # Differentiate Flux Equation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferentiateFluxEquation.CM.Construction

noncomputable section

section

/-! Differentiation of the actual weak elliptic equation by strong limits
of spatial difference quotients. The coefficient commutator is retained as
an explicit vector-valued flux. -/

open _root_.MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap LineDeriv ContDiff _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem coefficientGradient_difference_tendsto (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) {L : NNReal} (hL : LipschitzWith L A)
    {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (m : E)
    (u v : Lp ℂ 2 (volume : Measure E))
    (hv : Tendsto (fun t : ℝ => DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u) (𝓝[≠] 0) (𝓝 v)) :
    let M := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) A hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    let N := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (CoefficientDerivative.CM.Construction.coefficientDerivative A m)
      (CoefficientDerivative.CM.Construction.coefficientDerivative_continuous A hA m).aestronglyMeasurable
      (Filter.Eventually.of_forall (CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL m))
    Tendsto (fun t : ℝ => DifferenceProduct.CM.Construction.realL2Difference m t (M (EuclideanGradient.CM.Construction.sobolevVectorGradient b u))) (𝓝[≠] 0)
      (𝓝 (M (EuclideanGradient.CM.Construction.sobolevVectorGradient b v) + N (EuclideanGradient.CM.Construction.sobolevVectorGradient b u))) := by
  dsimp only
  have hD := ((EuclideanGradient.CM.Construction.sobolevVectorGradient b).continuous.tendsto v).comp hv
  have hT := CoefficientDerivative.CM.Construction.translatedCoefficientLp_tendsto_varying A hA.continuous hC m
    (fun t => EuclideanGradient.CM.Construction.sobolevVectorGradient b (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u)) (EuclideanGradient.CM.Construction.sobolevVectorGradient b v) hD
  have hR := CoefficientDerivative.CM.Construction.differenceCoefficientLp_tendsto A hA hL hC m (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)
  have h := hT.add hR
  have heq (t : ℝ) : DifferenceProduct.CM.Construction.realL2Difference m t
      (LpCoefficients.CM.Construction.boundedFieldLp A hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)) =
      LpCoefficients.CM.Construction.boundedFieldLp (DifferenceProduct.CM.Construction.translatedCoefficient A (t • m))
        (DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hA.continuous.aestronglyMeasurable (t • m))
        (DifferenceProduct.CM.Construction.translatedCoefficient_bound A (Filter.Eventually.of_forall hC) (t • m))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u)) +
      LpCoefficients.CM.Construction.boundedFieldLp (DifferenceProduct.CM.Construction.differenceCoefficient A m t)
        (DifferenceProduct.CM.Construction.differenceCoefficient_measurable A hA.continuous.aestronglyMeasurable m t)
        (DifferenceProduct.CM.Construction.differenceCoefficient_bound A (Filter.Eventually.of_forall hC) m t) (EuclideanGradient.CM.Construction.sobolevVectorGradient b u) := by
    rw [DifferenceProduct.CM.Construction.realL2Difference_coefficient_product, ← EuclideanGradient.CM.Construction.sobolevVectorGradient_difference]
  exact h.congr' (Filter.Eventually.of_forall (fun t => (heq t).symm))

omit [Fintype ι] in
theorem l2DifferenceQuotient_real_inner (m : E) (t : ℝ)
    (u v : Lp ℂ 2 (volume : Measure E)) :
    inner ℝ (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u) v = -inner ℝ u (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v) := by
  rw [← DifferenceProduct.CM.Construction.realL2Difference_eq_complex, ← DifferenceProduct.CM.Construction.realL2Difference_eq_complex]
  exact DifferenceProduct.CM.Construction.realL2Difference_inner m t u v

theorem euclidean_weak_equation_difference_test (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : AEStronglyMeasurable A (volume : Measure E))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (u f : Lp ℂ 2 (volume : Measure E)) (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricSolution b A u f)
    (m : E) (t : ℝ) (w : Lp ℂ 2 (volume : Measure E)) :
    inner ℝ (DifferenceProduct.CM.Construction.realL2Difference m t (LpCoefficients.CM.Construction.boundedFieldLp A hA hC (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)))
      (EuclideanGradient.CM.Construction.sobolevVectorGradient b w) =
      inner ℝ (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t f) (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w) := by
  let M := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) A hA hC
  let D := EuclideanGradient.CM.Construction.sobolevVectorGradient b
  let J := SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := ℂ) (by norm_num : (0 : ℝ) ≤ 1)
  have hweak (v : Lp ℂ 2 (volume : Measure E)) : inner ℝ (M (D u)) (D v) = inner ℝ f (J v) :=
    (CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hA hC (D u) (D v)).trans (hsol v)
  rw [DifferenceProduct.CM.Construction.realL2Difference_inner, ← EuclideanGradient.CM.Construction.sobolevVectorGradient_difference,
    hweak, ← DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolevEmbedding_comm,
    ← l2DifferenceQuotient_real_inner]

/-- The directional derivative of an H2 weak solution solves the
differentiated equation, with its genuine coefficient-derivative flux. -/
theorem euclidean_weak_solution_derivative (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) {L : NNReal} (hL : LipschitzWith L A)
    {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (m : E)
    (u f : Lp ℂ 2 (volume : Measure E)) (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricSolution b A u f)
    (hu : MemSobolev 2 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ)))
    (hf : MemSobolev 1 2 (f : 𝓢'(E, ℂ))) :
    let N := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (CoefficientDerivative.CM.Construction.coefficientDerivative A m)
      (CoefficientDerivative.CM.Construction.coefficientDerivative_continuous A hA m).aestronglyMeasurable
      (Filter.Eventually.of_forall (CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL m))
    ∃ v df : Lp ℂ 2 (volume : Measure E),
      SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v = SobolevDifferential.CM.Construction.sobolevL2Derivative m u ∧
      (df : 𝓢'(E, ℂ)) = ∂_{m} (f : 𝓢'(E, ℂ)) ∧
      EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricFluxSolution b A v df (-N (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)) := by
  dsimp only
  obtain ⟨v, hv, hvlim⟩ := SobolevDerivativeCoordinates.CM.Construction.h2_difference_tendsto_h1_derivative m u hu
  obtain ⟨fw, hfw⟩ := (SobolevDerivativeCoordinates.CM.Construction.memSobolev_l2_iff_embedding_range (by norm_num : (0 : ℝ) ≤ 1) f).mp hf
  let df := SobolevDifferential.CM.Construction.sobolevL2Derivative m fw
  have hdflim := DifferenceConvergence.CM.Construction.l2DifferenceQuotient_tendsto_derivative m fw
  rw [hfw] at hdflim
  refine ⟨v, df, hv, ?_, fun w => ?_⟩
  · rw [show (df : 𝓢'(E, ℂ)) = ∂_{m}
        (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) fw : 𝓢'(E, ℂ)) from
        SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution m fw, hfw]
  · have hlim := coefficientGradient_difference_tendsto b A hA hL hC m u v hvlim
    have hleft := hlim.inner (tendsto_const_nhds : Tendsto (fun _ : ℝ => EuclideanGradient.CM.Construction.sobolevVectorGradient b w)
      (𝓝[≠] 0) (𝓝 (EuclideanGradient.CM.Construction.sobolevVectorGradient b w))) (𝕜 := ℝ)
    have hright := hdflim.inner (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w) (𝓝[≠] 0)
      (𝓝 (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w))) (𝕜 := ℝ)
    have heq := tendsto_nhds_unique hleft (hright.congr' (Filter.Eventually.of_forall (fun t =>
      (euclidean_weak_equation_difference_test b A hA.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hC) u f hsol m t w).symm)))
    rw [inner_add_left] at heq
    rw [← CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)]
    change inner ℝ (LpCoefficients.CM.Construction.boundedFieldLp A hA.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC) (EuclideanGradient.CM.Construction.sobolevVectorGradient b v)) (EuclideanGradient.CM.Construction.sobolevVectorGradient b w) = _
    rw [inner_neg_left]
    linarith [heq]

end

/-! The strong-limit derivative of a weak equation with an actual flux
forcing, retaining both derivatives of that forcing and of the coefficients. -/

open _root_.MeasureTheory Filter
open scoped ContDiff _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem euclidean_weak_flux_difference_test (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : AEStronglyMeasurable A (volume : Measure E))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (u f : Lp ℂ 2 (volume : Measure E)) (g : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricFluxSolution b A u f g)
    (m : E) (t : ℝ) (w : Lp ℂ 2 (volume : Measure E)) :
    inner ℝ (DifferenceProduct.CM.Construction.realL2Difference m t (LpCoefficients.CM.Construction.boundedFieldLp A hA hC (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)))
      (EuclideanGradient.CM.Construction.sobolevVectorGradient b w) =
      inner ℝ (DifferenceProduct.CM.Construction.realL2Difference m t f) (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w) +
        inner ℝ (DifferenceProduct.CM.Construction.realL2Difference m t g) (EuclideanGradient.CM.Construction.sobolevVectorGradient b w) := by
  let M := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) A hA hC
  let D := EuclideanGradient.CM.Construction.sobolevVectorGradient b
  let J := SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := ℂ) (by norm_num : (0 : ℝ) ≤ 1)
  have hweak (v : Lp ℂ 2 (volume : Measure E)) :
      inner ℝ (M (D u)) (D v) = inner ℝ f (J v) + inner ℝ g (D v) :=
    (CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hA hC (D u) (D v)).trans (hsol v)
  rw [DifferenceProduct.CM.Construction.realL2Difference_inner, ← EuclideanGradient.CM.Construction.sobolevVectorGradient_difference,
    hweak, neg_add, ← DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolevEmbedding_comm,
    ← l2DifferenceQuotient_real_inner, EuclideanGradient.CM.Construction.sobolevVectorGradient_difference,
    ← DifferenceProduct.CM.Construction.realL2Difference_inner, DifferenceProduct.CM.Construction.realL2Difference_eq_complex]

theorem euclidean_weak_flux_derivative_of_limits (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) {L : NNReal} (hL : LipschitzWith L A)
    {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (m : E)
    (u f v df : Lp ℂ 2 (volume : Measure E))
    (g dg : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricFluxSolution b A u f g)
    (hv : Tendsto (fun t : ℝ => DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u) (𝓝[≠] 0) (𝓝 v))
    (hf : Tendsto (fun t : ℝ => DifferenceProduct.CM.Construction.realL2Difference m t f) (𝓝[≠] 0) (𝓝 df))
    (hg : Tendsto (fun t : ℝ => DifferenceProduct.CM.Construction.realL2Difference m t g) (𝓝[≠] 0) (𝓝 dg)) :
    let N := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (CoefficientDerivative.CM.Construction.coefficientDerivative A m)
      (CoefficientDerivative.CM.Construction.coefficientDerivative_continuous A hA m).aestronglyMeasurable
      (Filter.Eventually.of_forall (CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL m))
    EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricFluxSolution b A v df (dg - N (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)) := by
  dsimp only
  intro w
  have hlim := coefficientGradient_difference_tendsto b A hA hL hC m u v hv
  have hcD : Tendsto (fun _ : ℝ => EuclideanGradient.CM.Construction.sobolevVectorGradient b w) (𝓝[≠] 0)
      (𝓝 (EuclideanGradient.CM.Construction.sobolevVectorGradient b w)) := tendsto_const_nhds
  have hcJ : Tendsto (fun _ : ℝ => SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w)
      (𝓝[≠] 0) (𝓝 (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w)) := tendsto_const_nhds
  have hleft := hlim.inner hcD (𝕜 := ℝ)
  have hright := (hf.inner hcJ (𝕜 := ℝ)).add (hg.inner hcD (𝕜 := ℝ))
  have heq := tendsto_nhds_unique hleft (hright.congr' (Filter.Eventually.of_forall (fun t =>
    (euclidean_weak_flux_difference_test b A hA.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC) u f g hsol m t w).symm)))
  rw [inner_add_left] at heq
  rw [← CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)]
  change inner ℝ (LpCoefficients.CM.Construction.boundedFieldLp A hA.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hC) (EuclideanGradient.CM.Construction.sobolevVectorGradient b v)) (EuclideanGradient.CM.Construction.sobolevVectorGradient b w) = _
  rw [inner_sub_left]
  linarith [heq]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferentiateFluxEquation.CM.Construction
