import OAI.Analysis.HodgeTheory.Decomposition.VectorStrongGradient
import OAI.Analysis.HodgeTheory.Decomposition.VectorDerivativeCoordinates
import OAI.Analysis.HodgeTheory.Decomposition.VectorDifferentiateFlux

/-! # Vector Elliptic Regularity -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorEllipticRegularity.Constructions

noncomputable section

/-! All Sobolev orders for genuine vector weak elliptic flux equations
under integrated Gårding coercivity, proved by differentiating the equation. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv ContDiff

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem vector_elliptic_flux_regularity (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (c : PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a β : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hβ : 0 ≤ β)
    (hgard : ∀ y : E, ∀ v : Lp F 2 (volume : Measure E),
      a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b v‖ * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b v‖ ≤
        (∫ x, inner ℝ (A (x + y) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) +
          β * ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v‖ ^ 2)
    (u f : Lp F 2 (volume : Measure E))
    (g : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hsol : VectorEllipticEstimate.Constructions.IsVectorWeakFluxSolution b A u f g)
    (hf : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n f) (hg : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1) g) :
    MemSobolev ((n : ℝ) + 2) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F)) := by
  induction n generalizing u f g with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    apply VectorElliptic.Constructions.vector_elliptic_flux_h2_regularity b A hL hC ha hβ hgard u f g hsol
    intro i
    obtain ⟨_, _, hB, _⟩ := hg.2 i
    exact hB
  | succ n ih =>
    have hun := ih u f g hsol hf.1 hg.1
    have hu2 : MemSobolev 2 2
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F)) :=
      hun.mono (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hd (i : ι) : MemSobolev ((n : ℝ) + 2) 2
        (∂_{b i} (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F))) := by
      obtain ⟨v, hv, hvlim⟩ := VectorDerivativeCoordinates.Constructions.vector_h2_difference_tendsto_h1_derivative (b i) u hu2
      obtain ⟨df, hdflim, _, hdf⟩ := hf.2 i
      obtain ⟨dg, hdglim, _, hdg⟩ := hg.2 i
      let N := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (μ := (volume : Measure E)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative A (b i))
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative_continuous A hA (b i)).aestronglyMeasurable
        (Filter.Eventually.of_forall (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL (b i)))
      have hN : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1) (N (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u)) :=
        VectorStrongGradient.Constructions.vectorStrongSobolev_derivative_coefficient_gradient b n A c hA hc hL i u hun
      have hflux : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1) (dg - N (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u)) := by
        simpa only [sub_eq_add_neg] using hdg.add b (n + 1) (hN.neg b (n + 1))
      have hder := VectorDifferentiateFlux.Constructions.vector_weak_flux_derivative_of_limits b A hA hL hC (b i)
        u f v df g dg hsol hvlim hdflim hdglim
      rw [← AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution, ← hv]
      exact ih v df (dg - N (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u)) hder hdf hflux
    have h := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b ((n : ℝ) + 2)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F))).mpr ⟨hun, hd⟩
    have hn : ((n + 1 : ℕ) : ℝ) + 2 = ((n : ℝ) + 2) + 1 := by push_cast; ring
    rw [hn]
    exact h

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorEllipticRegularity.Constructions
