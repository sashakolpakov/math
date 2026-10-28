import OAI.Analysis.HodgeTheory.Decomposition.VectorLocalElliptic
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts

/-! # Vector Differentiate Flux -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorDifferentiateFlux.Constructions

noncomputable section

/-! Differentiating the actual vector weak flux equation by strong L²
limits, including the derivative of the variable principal coefficient. -/

open _root_.MeasureTheory Filter
open scoped ContDiff _root_.Topology
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts.CM.Construction

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem vector_weak_flux_difference_test (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (hA : AEStronglyMeasurable A volume) {C : ℝ} (hC : ∀ᵐ x ∂volume, ‖A x‖ ≤ C)
    (u f : Lp F 2 (volume : Measure E)) (g : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hsol : VectorEllipticEstimate.Constructions.IsVectorWeakFluxSolution b A u f g)
    (m : E) (t : ℝ) (w : Lp F 2 (volume : Measure E)) :
    inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp A hA hC (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u)))
      (VectorGradient.Constructions.vectorSobolevGradient (F := F) b w) =
      inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t f) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w) +
        inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t g) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b w) := by
  let M := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp (p := 2) A hA hC
  let D := VectorGradient.Constructions.vectorSobolevGradient (F := F) b
  let J := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := F) (by norm_num : (0 : ℝ) ≤ 1)
  have hweak (v : Lp F 2 (volume : Measure E)) :
      inner ℝ (M (D u)) (D v) = inner ℝ f (J v) + inner ℝ g (D v) :=
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hA hC (D u) (D v)).trans (hsol v)
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference_inner, ← VectorGradient.Constructions.vectorSobolevGradient_difference, hweak, neg_add,
    ← VectorDifferenceBounds.Constructions.vectorL2DifferenceQuotient_sobolevEmbedding_comm,
    ← VectorLocalElliptic.Constructions.realL2Difference_eq_vector m (-t) (J w), ← AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference_inner,
    VectorGradient.Constructions.vectorSobolevGradient_difference, ← AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference_inner]

theorem vector_weak_flux_derivative_of_limits (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (hA : ContDiff ℝ ∞ A) {L : NNReal} (hL : LipschitzWith L A)
    {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (m : E)
    (u f v df : Lp F 2 (volume : Measure E))
    (g dg : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hsol : VectorEllipticEstimate.Constructions.IsVectorWeakFluxSolution b A u f g)
    (hv : Tendsto (fun t : ℝ => VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u) (𝓝[≠] 0) (𝓝 v))
    (hf : Tendsto (fun t : ℝ => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t f) (𝓝[≠] 0) (𝓝 df))
    (hg : Tendsto (fun t : ℝ => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t g) (𝓝[≠] 0) (𝓝 dg)) :
    let N := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative A m)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative_continuous A hA m).aestronglyMeasurable
      (Filter.Eventually.of_forall (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL m))
    VectorEllipticEstimate.Constructions.IsVectorWeakFluxSolution b A v df (dg - N (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u)) := by
  dsimp only
  intro w
  have hDlim : Tendsto (fun t : ℝ => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u))
      (𝓝[≠] 0) (𝓝 (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v)) := by
    simpa only [Function.comp_def, VectorGradient.Constructions.vectorSobolevGradient_difference] using
      ((VectorGradient.Constructions.vectorSobolevGradient (F := F) b).continuous.tendsto v).comp hv
  have hlim := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts.CM.Construction.coefficient_product_difference_tendsto A hA hL hC m
    (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v) hDlim
  have hcD : Tendsto (fun _ : ℝ => VectorGradient.Constructions.vectorSobolevGradient (F := F) b w) (𝓝[≠] 0)
      (𝓝 (VectorGradient.Constructions.vectorSobolevGradient (F := F) b w)) := tendsto_const_nhds
  have hcJ : Tendsto (fun _ : ℝ => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w)
      (𝓝[≠] 0) (𝓝 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w)) := tendsto_const_nhds
  have hleft := hlim.inner hcD (𝕜 := ℝ)
  have hright := (hf.inner hcJ (𝕜 := ℝ)).add (hg.inner hcD (𝕜 := ℝ))
  have heq := tendsto_nhds_unique hleft (hright.congr' (Filter.Eventually.of_forall (fun t =>
    (vector_weak_flux_difference_test b A hA.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC) u f g hsol m t w).symm)))
  rw [inner_add_left] at heq
  rw [← AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)]
  change inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp A hA.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hC) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v)) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b w) = _
  rw [inner_sub_left]
  linarith only [heq]

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorDifferentiateFlux.Constructions
