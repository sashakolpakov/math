import OAI.Analysis.HodgeTheory.Decomposition.GradientRows
import OAI.Analysis.HodgeTheory.Decomposition.LocalRellich

/-! # Schwartz Gradient Support -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SchwartzGradientSupport.Constructions

noncomputable section

section

/-! Actual first-order chart operators on Schwartz functions agree with
the rows of the genuine normalized Sobolev gradient. -/

open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap BigOperators

variable {E F G ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem vectorSobolevGradient_schwartz_normalization (b : OrthonormalBasis ι ℝ E)
    (f : 𝓢(E, F)) :
    ∀ᵐ x ∂(volume : Measure E),
      (2 * Real.pi * Complex.I : ℂ) • VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x =
        WithLp.toLp 2 (fun i => (∂_{b i} f : 𝓢(E, F)) x) := by
  let u := VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f
  have hc : ∀ᵐ x ∂(volume : Measure E), ∀ i : ι,
      (2 * Real.pi * Complex.I : ℂ) • VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u i x =
        (∂_{b i} f : 𝓢(E, F)) x := by
    apply ae_all_iff.mpr
    intro i
    have hD := VectorEmbeddingRange.Constructions.vectorSobolevL2Derivative_schwartz (b i) f
    have hκ := VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient_derivative b u i
    rw [hD] at hκ
    filter_upwards [Lp.coeFn_smul (2 * Real.pi * Complex.I : ℂ) (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u i),
      (∂_{b i} f : 𝓢(E, F)).coeFn_toLp 2 volume] with x hx hfx
    rw [← hκ] at hx
    exact hx.symm.trans hfx
  filter_upwards [FiniteLp.Constructions.finiteLpSynthesis_coe (𝕜 := ℂ) (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u), hc]
    with x hx hc
  change (2 * Real.pi * Complex.I : ℂ) •
    FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u) x = _
  rw [hx]
  apply PiLp.ext
  exact hc

theorem normalizedGradientRow_schwartz {κ : Type*} [Fintype κ] (b : OrthonormalBasis ι ℝ E)
    (S : E → ι → (EuclideanSpace ℂ κ) →L[ℝ] G) (f : 𝓢(E, EuclideanSpace ℂ κ)) :
    ∀ᵐ x ∂(volume : Measure E),
      GradientRows.Constructions.normalizedGradientRow (S x) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x) =
        ∑ i, S x i ((∂_{b i} f : 𝓢(E, EuclideanSpace ℂ κ)) x) := by
  filter_upwards [vectorSobolevGradient_schwartz_normalization b f] with x hx
  rw [GradientRows.Constructions.normalizedGradientRow_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (S x i) (congrArg (fun v : PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ) => v i) hx)

theorem vectorSobolevGradient_schwartz_energy (b : OrthonormalBasis ι ℝ E)
    (f : 𝓢(E, F)) :
    ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 *
        ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)‖ ^ 2 =
      ∑ i, ∫ x, ‖(∂_{b i} f : 𝓢(E, F)) x‖ ^ 2 := by
  rw [VectorGradient.Constructions.vectorSobolevGradient_norm, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_pow, ← norm_smul, ← VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient_derivative,
    VectorEmbeddingRange.Constructions.vectorSobolevL2Derivative_schwartz, LocalRellich.Constructions.schwartz_toLp_norm_sq]

end

/-! The genuine L² gradient of a Schwartz coefficient field vanishes
almost everywhere outside the support of that field. -/

open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vectorSobolevGradient_schwartz_zero_off_support (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, F)) :
    ∀ᵐ x ∂(volume : Measure E), x ∉ tsupport f →
      VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x = 0 := by
  have hκ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  filter_upwards [vectorSobolevGradient_schwartz_normalization b f] with x hx hs
  apply (smul_eq_zero.mp (show (2 * Real.pi * Complex.I : ℂ) •
    VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x = 0 from ?_)).resolve_left hκ
  rw [hx]
  apply PiLp.ext
  intro i
  change (∂_{b i} f : 𝓢(E, F)) x = 0
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_of_notMem_tsupport ℝ hs, zero_apply]

end

end OAI.Analysis.HodgeTheory.Decomposition.SchwartzGradientSupport.Constructions
