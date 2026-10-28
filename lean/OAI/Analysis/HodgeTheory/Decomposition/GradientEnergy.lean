import OAI.Analysis.HodgeTheory.Decomposition.WeightedPlancherel
import OAI.Analysis.HodgeTheory.Decomposition.CoordinateLp

/-! # Gradient Energy -/

namespace OAI.Analysis.HodgeTheory.Decomposition.GradientEnergy.Constructions

noncomputable section

/-! The first-order Fourier moment equals the squared L² norm of the actual
directional derivatives, with the genuine Fourier normalization. -/

open FourierTransform LineDeriv _root_.MeasureTheory
open scoped SchwartzMap BigOperators

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

omit [CompleteSpace F] in
theorem schwartz_normsq_integrable (f : 𝓢(E, F)) : Integrable (fun x => ‖f x‖ ^ 2) volume := by
  apply (Complex.reCLM.integrable_comp (WeightedPlancherel.Constructions.schwartz_inner_integrable f f)).congr
  exact Filter.Eventually.of_forall (fun x => inner_self_eq_norm_sq (𝕜 := ℂ) (f x))

theorem schwartz_normsq_plancherel (f : 𝓢(E, F)) :
    (∫ x, ‖f x‖ ^ 2) = ∫ ξ, ‖𝓕 f ξ‖ ^ 2 := by
  calc
    _ = ‖f.toLp 2 volume‖ ^ 2 := (CoordinateLp.Constructions.memLp_toLp_norm_sq (f : E → F) (f.memLp 2 volume)).symm
    _ = ‖(𝓕 f).toLp 2 volume‖ ^ 2 := by rw [← SchwartzMap.toLp_fourier_eq, Lp.norm_fourier_eq]
    _ = _ := CoordinateLp.Constructions.memLp_toLp_norm_sq ((𝓕 f : 𝓢(E, F)) : E → F) ((𝓕 f).memLp 2 volume)

omit [CompleteSpace F] in
theorem schwartz_directional_fourier_norm (f : 𝓢(E, F)) (m ξ : E) :
    ‖𝓕 (∂_{m} f) ξ‖ ^ 2 =
      ‖2 * Real.pi * Complex.I‖ ^ 2 * (inner ℝ ξ m) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have htemp : (fun x : E => inner ℝ x m).HasTemperateGrowth := Function.hasTemperateGrowth_inner_left m
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply htemp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem schwartz_gradient_energy (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, F)) :
    (∑ i, ∫ x, ‖∂_{b i} f x‖ ^ 2) =
      ‖2 * Real.pi * Complex.I‖ ^ 2 * ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  calc
    _ = ∑ i, ∫ ξ, ‖𝓕 (∂_{b i} f) ξ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact schwartz_normsq_plancherel (∂_{b i} f)
    _ = ∫ ξ, ∑ i, ‖𝓕 (∂_{b i} f) ξ‖ ^ 2 :=
      (integral_finsetSum _ (fun i _ => schwartz_normsq_integrable (𝓕 (∂_{b i} f)))).symm
    _ = ∫ ξ, ‖2 * Real.pi * Complex.I‖ ^ 2 * (‖ξ‖ ^ 2 * ‖𝓕 f ξ‖ ^ 2) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ξ
      dsimp only
      simp_rw [schwartz_directional_fourier_norm]
      rw [← Finset.sum_mul, ← Finset.mul_sum, b.sum_sq_inner_left]
      ring
    _ = _ := integral_const_mul _ _

end

end OAI.Analysis.HodgeTheory.Decomposition.GradientEnergy.Constructions
