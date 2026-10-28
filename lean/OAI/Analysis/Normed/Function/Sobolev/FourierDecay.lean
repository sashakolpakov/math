import OAI.Analysis.Normed.Function.Sobolev.FourierRegularity
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

/-- A polynomial decay bound of order strictly above dimension plus the
moment order makes that Fourier moment integrable. -/
theorem integrable_moment_of_polynomial_decay {d k m : ℕ} {F : Space d → ℂ}
    (hF : AEStronglyMeasurable F) {C : ℝ} (_ : 0 ≤ C)
    (hk : d + m < k)
    (hbound : ∀ ξ, (1 + ‖ξ‖) ^ k * ‖F ξ‖ ≤ C) :
    Integrable (fun ξ ↦ ‖ξ‖ ^ m * ‖F ξ‖) := by
  have hdim : (Module.finrank ℝ (Space d) : ℝ) < (k : ℝ) - m := by
    have hcast : (d : ℝ) + m < k := by exact_mod_cast hk
    simpa only [Space, finrank_euclideanSpace, Fintype.card_fin] using (lt_sub_iff_add_lt.mpr hcast)
  have hw : Integrable (fun ξ : Space d ↦ C * (1 + ‖ξ‖) ^ (-((k : ℝ) - m))) :=
    (integrable_one_add_norm (μ := volume) hdim).const_mul C
  apply hw.mono' ((continuous_norm.pow m).aestronglyMeasurable.mul hF.norm)
  exact Eventually.of_forall fun ξ ↦ by
    have hb : 0 < 1 + ‖ξ‖ := by positivity
    have hbp : 0 < (1 + ‖ξ‖) ^ k := pow_pos hb k
    have hdiv : ‖F ξ‖ ≤ C / (1 + ‖ξ‖) ^ k := by
      apply (le_div_iff₀ hbp).mpr
      simpa only [mul_comm] using hbound ξ
    have hm : ‖ξ‖ ^ m ≤ (1 + ‖ξ‖) ^ m := by
      apply pow_le_pow_left₀ (norm_nonneg ξ)
      linarith
    have hpow : (1 + ‖ξ‖) ^ (-((k : ℝ) - m)) =
        (1 + ‖ξ‖) ^ m / (1 + ‖ξ‖) ^ k := by
      rw [neg_sub, Real.rpow_sub hb, Real.rpow_natCast, Real.rpow_natCast]
    calc
      ‖‖ξ‖ ^ m * ‖F ξ‖‖ = ‖ξ‖ ^ m * ‖F ξ‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (1 + ‖ξ‖) ^ m * (C / (1 + ‖ξ‖) ^ k) :=
        mul_le_mul hm hdiv (norm_nonneg _) (by positivity)
      _ = C * (1 + ‖ξ‖) ^ (-((k : ℝ) - m)) := by rw [hpow]; ring

/-- The non-sharp strict threshold `k > d + q` is sufficient for a C^q
representative. The decay bound is the conclusion to be supplied by the
weak-derivative identities, not a smoothness hypothesis on the input. -/
theorem exists_contDiff_representative_of_polynomial_fourier_decay {d k q : ℕ}
    {f : Space d → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2)
    {C : ℝ} (hC : 0 ≤ C) (hk : d + q < k)
    (hbound : ∀ ξ, (1 + ‖ξ‖) ^ k * ‖𝓕 f ξ‖ ≤ C) :
    ∃ g : Space d → ℂ, ContDiff ℝ q g ∧ f =ᵐ[volume] g := by
  apply exists_contDiff_representative_of_fourier_moments (N := q) hf hf₂
  intro m hm
  have hm' : m ≤ q := by exact_mod_cast hm
  exact integrable_moment_of_polynomial_decay
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf).aestronglyMeasurable hC (by omega) hbound

theorem exists_C2_representative_of_polynomial_fourier_decay {d k : ℕ}
    {f : Space d → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2)
    {C : ℝ} (hC : 0 ≤ C) (hk : d + 2 < k)
    (hbound : ∀ ξ, (1 + ‖ξ‖) ^ k * ‖𝓕 f ξ‖ ≤ C) :
    ∃ g : Space d → ℂ, ContDiff ℝ 2 g ∧ f =ᵐ[volume] g :=
  exists_contDiff_representative_of_polynomial_fourier_decay hf hf₂ hC hk hbound

end OAI.Analysis.Normed.Function.Sobolev
