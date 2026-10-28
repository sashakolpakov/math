import OAI.Analysis.HodgeTheory.Decomposition.VectorEllipticEstimate
import OAI.Analysis.HodgeTheory.Decomposition.VectorDifferenceCriterion

/-! # Vector Elliptic -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorElliptic.Constructions

noncomputable section

/-! H2 regularity for the actual Euclidean weak metric equation with
uniformly elliptic Lipschitz coefficients and L2 forcing. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv _root_.Topology

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vectorSobolevL2Derivative_norm_le_gradient (b : OrthonormalBasis ι ℝ E)
    (i : ι) (u : Lp F 2 (volume : Measure E)) :
    ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) u‖ ≤ (2 * Real.pi) * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b u‖ := by
  rw [VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient_derivative, norm_smul, VectorGradient.Constructions.vectorSobolevGradient_norm]
  have hκ : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hκ]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u) i) (by positivity)

variable [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- A weak solution of the genuine divergence-form metric equation gains a
second distributional Sobolev derivative. -/
theorem vector_elliptic_flux_h2_regularity (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F)) {L : NNReal}
    (hA : LipschitzWith L A) {C a c : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hc : 0 ≤ c)
    (hgard : ∀ y : E, ∀ v : Lp F 2 (volume : Measure E),
      a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b v‖ * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b v‖ ≤
        (∫ x, inner ℝ (A (x + y) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) +
          c * ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v‖ ^ 2)
    (u f : Lp F 2 (volume : Measure E))
    (g : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hsol : VectorEllipticEstimate.Constructions.IsVectorWeakFluxSolution b A u f g)
    (hg : ∀ i : ι, ∃ B : ℝ, ∀ t : ℝ, ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference (b i) t g‖ ≤ B) :
    MemSobolev 2 2
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : Lp F 2 volume) : 𝓢'(E, F)) := by
  let J := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := F) (by norm_num : (0 : ℝ) ≤ 1)
  have hu : MemSobolev 1 2 (J u : 𝓢'(E, F)) := by
    change MemSobolev 1 2 ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) : 𝓢'(E, F))
    rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff, neg_add_cancel]
    exact memSobolev_zero_iff.mpr ⟨u, rfl⟩
  have hd (j : ι) : MemSobolev 1 2 (∂_{b j} (J u : 𝓢'(E, F))) := by
    rw [← AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution]
    apply VectorDifferenceCriterion.Constructions.vectorMemSobolev_one_of_difference_bounds b
    intro i
    obtain ⟨B₀, hB₀⟩ := hg i
    obtain ⟨B, hB⟩ := VectorEllipticEstimate.Constructions.vector_elliptic_flux_difference_gradient_bound b A hA hC ha hc hgard u f g hsol (b i) hB₀
    refine ⟨2 * Real.pi * B, Filter.Eventually.of_forall (fun t => ?_)⟩
    rw [VectorDifferenceBounds.Constructions.vectorL2DifferenceQuotient_sobolevDerivative_comm]
    exact (vectorSobolevL2Derivative_norm_le_gradient b j (VectorDifferences.Constructions.vectorL2DifferenceQuotient (b i) t u)).trans
      (mul_le_mul_of_nonneg_left (hB t) (by positivity))
  have h := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b 1 (J u : 𝓢'(E, F))).mpr ⟨hu, hd⟩
  norm_num only [one_add_one_eq_two] at h
  exact h

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorElliptic.Constructions
