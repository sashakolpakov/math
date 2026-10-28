import OAI.Analysis.HodgeTheory.Decomposition.FourierOperator
import Mathlib.Analysis.Fourier.LpSpace

/-! # Weighted Plancherel -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeightedPlancherel.Constructions

noncomputable section

/-! Plancherel identities with constant complex-linear metric coefficients. -/

open FourierTransform _root_.MeasureTheory
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem schwartz_inner_integrable (f g : 𝓢(E, F)) : Integrable (fun x => inner ℂ (f x) (g x)) volume := by
  apply (L2.integrable_inner (𝕜 := ℂ) (f.toLp 2 volume) (g.toLp 2 volume)).congr
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hfx hgx
  rw [hfx, hgx]

theorem schwartz_weighted_plancherel (A : F →L[ℂ] F) (f : 𝓢(E, F)) :
    (∫ x, inner ℂ (A (f x)) (f x)) =
      ∫ ξ, inner ℂ (A (𝓕 f ξ)) (𝓕 f ξ) := by
  have h := Lp.inner_fourier_eq ((SchwartzMap.postcompCLM A f).toLp 2) (f.toLp 2)
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
    FourierOperator.Constructions.fourier_postcomp_schwartz] at h
  rw [SchwartzMap.inner_toL2_toL2_eq (SchwartzMap.postcompCLM A (𝓕 f)) (𝓕 f) volume,
    SchwartzMap.inner_toL2_toL2_eq (SchwartzMap.postcompCLM A f) f volume] at h
  exact h.symm

theorem schwartz_weighted_plancherel_re (A : F →L[ℂ] F) (f : 𝓢(E, F)) :
    (∫ x, (inner ℂ (A (f x)) (f x)).re) =
      ∫ ξ, (inner ℂ (A (𝓕 f ξ)) (𝓕 f ξ)).re := by
  calc
    _ = RCLike.re (∫ x, inner ℂ (A (f x)) (f x)) :=
      integral_re (schwartz_inner_integrable (SchwartzMap.postcompCLM A f) f)
    _ = RCLike.re (∫ ξ, inner ℂ (A (𝓕 f ξ)) (𝓕 f ξ)) :=
      congrArg Complex.re (schwartz_weighted_plancherel A f)
    _ = _ := (integral_re (schwartz_inner_integrable (SchwartzMap.postcompCLM A (𝓕 f)) (𝓕 f))).symm

omit [CompleteSpace F] in
theorem complex_weighted_inner_smul (A : F →L[ℂ] F) (u : F) (c : ℂ) :
    (inner ℂ (A (c • u)) (c • u)).re = ‖c‖ ^ 2 * (inner ℂ (A u) u).re := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
  change ((star c * c) * inner ℂ (A u) u).re = _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end

end OAI.Analysis.HodgeTheory.Decomposition.WeightedPlancherel.Constructions
