import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate

/-! # Elliptic -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Elliptic.CM.Construction

noncomputable section

/-! H2 regularity for the actual Euclidean weak metric equation with
uniformly elliptic Lipschitz coefficients and L2 forcing. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem sobolevL2Derivative_norm_le_vectorGradient (b : OrthonormalBasis ι ℝ E)
    (i : ι) (u : Lp ℂ 2 (volume : Measure E)) :
    ‖SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) u‖ ≤ (2 * Real.pi) * ‖EuclideanGradient.CM.Construction.sobolevVectorGradient b u‖ := by
  rw [FourierEnergy.CM.Construction.sobolevNormalizedGradient_derivative, norm_smul, EuclideanGradient.CM.Construction.sobolevVectorGradient_norm]
  have hκ : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hκ]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u) i) (by positivity)

/-- A weak solution of the genuine divergence-form metric equation gains a
second distributional Sobolev derivative. -/
theorem euclidean_elliptic_flux_h2_regularity (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) {L : NNReal}
    (hA : LipschitzWith L A) {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (u f : Lp ℂ 2 (volume : Measure E))
    (g : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricFluxSolution b A u f g)
    (hg : ∀ i : ι, ∃ B : ℝ, ∀ t : ℝ, ‖DifferenceProduct.CM.Construction.realL2Difference (b i) t g‖ ≤ B) :
    MemSobolev 2 2
      ((SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : Lp ℂ 2 volume) : 𝓢'(E, ℂ)) := by
  let J := SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := ℂ) (by norm_num : (0 : ℝ) ≤ 1)
  have hu : MemSobolev 1 2 (J u : 𝓢'(E, ℂ)) := by
    change MemSobolev 1 2 ((SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) : 𝓢'(E, ℂ))
    rw [SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff, neg_add_cancel]
    exact memSobolev_zero_iff.mpr ⟨u, rfl⟩
  have hd (j : ι) : MemSobolev 1 2 (∂_{b j} (J u : 𝓢'(E, ℂ))) := by
    rw [← SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution]
    apply DifferenceCriterion.CM.Construction.memSobolev_one_of_difference_bounds b
    intro i
    obtain ⟨B₀, hB₀⟩ := hg i
    obtain ⟨B, hB⟩ := EllipticDifferenceEstimate.CM.Construction.elliptic_flux_difference_gradient_bound b A hA hC ha hpos u f g hsol (b i) hB₀
    refine ⟨2 * Real.pi * B, Filter.Eventually.of_forall (fun t => ?_)⟩
    rw [DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolevDerivative_comm]
    exact (sobolevL2Derivative_norm_le_vectorGradient b j (DifferenceQuotients.CM.Construction.l2DifferenceQuotient (b i) t u)).trans
      (mul_le_mul_of_nonneg_left (hB t) (by positivity))
  have h := (SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b 1 (J u : 𝓢'(E, ℂ))).mpr ⟨hu, hd⟩
  norm_num only [one_add_one_eq_two] at h
  exact h

theorem euclidean_elliptic_h2_regularity (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) {L : NNReal}
    (hA : LipschitzWith L A) {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (u f : Lp ℂ 2 (volume : Measure E)) (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricSolution b A u f) :
    MemSobolev 2 2
      ((SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : Lp ℂ 2 volume) : 𝓢'(E, ℂ)) := by
  apply euclidean_elliptic_flux_h2_regularity b A hA hC ha hpos u f 0
  · intro v
    simpa only [inner_zero_left, add_zero] using hsol v
  · intro i
    exact ⟨0, fun t => by simp⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Elliptic.CM.Construction
