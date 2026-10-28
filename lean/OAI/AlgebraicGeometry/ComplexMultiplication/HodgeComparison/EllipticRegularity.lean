import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferentiateFluxEquation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth

/-! # Elliptic Regularity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticRegularity.CM.Construction

noncomputable section

/-! Elliptic regularity at every Sobolev order for the actual Euclidean
metric equation, and a genuine smooth representative for smooth forcing. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv ContDiff

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem strongSobolev_gradient_of_memSobolev (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (u : Lp ℂ 2 (volume : Measure E))
    (hu : MemSobolev ((n : ℝ) + 1) 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ))) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (EuclideanGradient.CM.Construction.sobolevVectorGradient b u) := by
  rw [SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff,
    show -(1 : ℝ) + ((n : ℝ) + 1) = n by ring] at hu
  exact StrongSobolevOperators.CM.Construction.strongSobolev_vectorGradient b n ((StrongSobolev.CM.Construction.strongSobolev_iff_memSobolev b n u).mpr hu)

theorem strongSobolev_derivative_coefficient_gradient (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) (i : ι)
    (u : Lp ℂ 2 (volume : Measure E))
    (hu : MemSobolev ((n : ℝ) + 2) 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ))) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1)
      (LpCoefficients.CM.Construction.boundedFieldLp (CoefficientDerivative.CM.Construction.coefficientDerivative A (b i))
        (CoefficientDerivative.CM.Construction.coefficientDerivative_continuous A hA (b i)).aestronglyMeasurable
        (Filter.Eventually.of_forall (CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL (b i)))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)) := by
  have hdA := SmoothCoefficientDerivatives.CM.Construction.coefficientDerivative_smooth A hA (b i)
  have hdAc : HasCompactSupport (fun x => CoefficientDerivative.CM.Construction.coefficientDerivative A (b i) x - 0) := by
    simpa only [sub_zero] using SmoothCoefficientDerivatives.CM.Construction.coefficientDerivative_compact_support A c hc (b i)
  obtain ⟨Ld, hLd⟩ := SmoothCoefficientDerivatives.CM.Construction.coefficientDerivative_lipschitz A c hA hc (b i)
  apply StrongCoefficientProducts.CM.Construction.strongSobolev_coefficient_product b (n + 1) (CoefficientDerivative.CM.Construction.coefficientDerivative A (b i)) 0 hdA hdAc hLd
    (CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL (b i))
  apply strongSobolev_gradient_of_memSobolev b (n + 1) u
  simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using hu

/-- Hn scalar forcing and H(n+1) flux forcing give H(n+2) regularity of the
actual weak solution, for every natural n. -/
theorem euclidean_elliptic_flux_regularity (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (u f : Lp ℂ 2 (volume : Measure E))
    (g : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricFluxSolution b A u f g)
    (hf : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n f) (hg : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1) g) :
    MemSobolev ((n : ℝ) + 2) 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ)) := by
  induction n generalizing u f g with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    apply Elliptic.CM.Construction.euclidean_elliptic_flux_h2_regularity b A hL hC ha hpos u f g hsol
    intro i
    obtain ⟨_, _, hB, _⟩ := hg.2 i
    exact hB
  | succ n ih =>
    have hun := ih u f g hsol hf.1 hg.1
    have hu2 : MemSobolev 2 2
        (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ)) :=
      hun.mono (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hd (i : ι) : MemSobolev ((n : ℝ) + 2) 2
        (∂_{b i} (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ))) := by
      obtain ⟨v, hv, hvlim⟩ := SobolevDerivativeCoordinates.CM.Construction.h2_difference_tendsto_h1_derivative (b i) u hu2
      obtain ⟨df, hdflim, _, hdf⟩ := hf.2 i
      obtain ⟨dg, hdglim, _, hdg⟩ := hg.2 i
      let N := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (μ := (volume : Measure E)) (CoefficientDerivative.CM.Construction.coefficientDerivative A (b i))
        (CoefficientDerivative.CM.Construction.coefficientDerivative_continuous A hA (b i)).aestronglyMeasurable
        (Filter.Eventually.of_forall (CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL (b i)))
      have hN : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1) (N (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)) :=
        strongSobolev_derivative_coefficient_gradient b n A c hA hc hL i u hun
      have hflux : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1) (dg - N (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)) := by
        simpa only [sub_eq_add_neg] using hdg.add b (n + 1) (hN.neg b (n + 1))
      have hder := DifferentiateFluxEquation.CM.Construction.euclidean_weak_flux_derivative_of_limits b A hA hL hC (b i)
        u f v df g dg hsol hvlim hdflim hdglim
      rw [← SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution, ← hv]
      exact ih v df (dg - N (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)) hder hdf hflux
    have h := (SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b ((n : ℝ) + 2)
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ))).mpr ⟨hun, hd⟩
    have hn : ((n + 1 : ℕ) : ℝ) + 2 = ((n : ℝ) + 2) + 1 := by push_cast; ring
    rw [hn]
    exact h

theorem euclidean_elliptic_regularity (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (u f : Lp ℂ 2 (volume : Measure E)) (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricSolution b A u f)
    (hf : MemSobolev (n : ℝ) 2 (f : 𝓢'(E, ℂ))) :
    MemSobolev ((n : ℝ) + 2) 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ)) := by
  apply euclidean_elliptic_flux_regularity b n A c hA hc hL hC ha hpos u f 0
  · intro v
    simpa only [inner_zero_left, add_zero] using hsol v
  · exact (StrongSobolev.CM.Construction.strongSobolev_iff_memSobolev b n f).mpr hf
  · exact StrongSobolev.CM.Construction.strongSobolev_zero b (n + 1)

theorem euclidean_elliptic_smooth_representative (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (u f : Lp ℂ 2 (volume : Measure E)) (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricSolution b A u f)
    (hf : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (f : 𝓢'(E, ℂ))) :
    ∃ v : BoundedContinuousFunction E ℂ, SobolevInv.CM.Construction.boundedFunctionDistribution v =
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ)) ∧
      ContDiff ℝ (⊤ : ℕ∞) (v : E → ℂ) := by
  apply Smooth.CM.Construction.sobolev_all_orders_smooth
  intro n
  exact (euclidean_elliptic_regularity b n A c hA hc hL hC ha hpos u f hsol (hf n)).mono (by linarith)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticRegularity.CM.Construction
