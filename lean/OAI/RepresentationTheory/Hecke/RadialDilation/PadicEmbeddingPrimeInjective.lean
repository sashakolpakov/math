import OAI.RepresentationTheory.Hecke.RadialDilation.PadicEmbeddingMem
import OAI.RepresentationTheory.Hecke.RadialDilation.NormalizedValuationEquality

/-! # Padic Embedding Prime Injective -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PadicEmbeddingPrimeInjective.Realization

noncomputable section

section

/-! The induced prime valuation is exactly the standard p-adic valuation of the embedded element. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField WithZero

variable (q : ℕ) [Fact q.Prime]

theorem padic_mulValuation_le_one_iff (x : ℚ_[q]) :
    Padic.mulValuation x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  change (if x = 0 then 0 else exp (-x.valuation)) ≤ 1 ↔ _
  rw [ite_eq_right hx, Padic.norm_le_one_iff_val_nonneg, ← exp_zero, exp_le_exp]
  exact neg_nonpos

theorem padic_mulValuation_prime : Padic.mulValuation (q : ℚ_[q]) = exp (-1 : ℤ) := by
  change (if (q : ℚ_[q]) = 0 then 0 else exp (-(q : ℚ_[q]).valuation)) = _
  rw [ite_eq_right (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero), Padic.valuation_p]

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]

theorem padicEmbeddingPrime_valuation (σ : E →ₐ[ℚ] ℚ_[q]) :
    (PadicEmbeddingMem.Realization.padicEmbeddingPrime q σ).valuation E = (Padic.mulValuation (p := q)).comap σ.toRingHom := by
  have he : ((PadicEmbeddingMem.Realization.padicEmbeddingPrime q σ).valuation E).IsEquiv
      ((Padic.mulValuation (p := q)).comap σ.toRingHom) := by
    apply Valuation.isEquiv_of_val_le_one
    intro x
    rw [PadicEmbeddingMem.Realization.padicEmbedding_valuation_le_one_iff]
    exact (padic_mulValuation_le_one_iff q (σ x)).symm
  obtain ⟨u, hu⟩ := (PadicEmbeddingMem.Realization.padicEmbeddingPrime q σ).valuation_exists_uniformizer E
  apply NormalizedValuationEquality.Realization.normalized_discrete_valuations_equal _ _ he u (q : E) hu
  change Padic.mulValuation (σ (q : E)) = _
  rw [map_natCast, padic_mulValuation_prime]

theorem padicEmbedding_norm_of_valuation (σ : E →ₐ[ℚ] ℚ_[q]) (x : E) (n : ℤ)
    (hx : (PadicEmbeddingMem.Realization.padicEmbeddingPrime q σ).valuation E x = exp n) :
    ‖σ x‖ = (q : ℝ) ^ n := by
  rw [padicEmbeddingPrime_valuation] at hx
  change Padic.mulValuation (σ x) = exp n at hx
  have hx0 : σ x ≠ 0 := by
    intro he
    rw [he, map_zero] at hx
    exact WithZero.coe_ne_zero hx.symm
  rw [Padic.norm_eq_zpow_log_mulValuation hx0, hx, log_exp]

end

/-! Distinct embeddings into the p-adic field induce distinct finite primes. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField

variable (q : ℕ) [Fact q.Prime] {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]

theorem padicEmbedding_same_prime_norm (σ τ : E →ₐ[ℚ] ℚ_[q])
    (h : PadicEmbeddingMem.Realization.padicEmbeddingPrime q σ = PadicEmbeddingMem.Realization.padicEmbeddingPrime q τ) (x : E) : ‖σ x‖ = ‖τ x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have he := congrArg (fun w : HeightOneSpectrum (𝓞 E) => w.valuation E x) h
  rw [padicEmbeddingPrime_valuation, padicEmbeddingPrime_valuation] at he
  change Padic.mulValuation (σ x) = Padic.mulValuation (τ x) at he
  rw [Padic.norm_eq_zpow_log_mulValuation ((map_ne_zero σ).mpr hx),
    Padic.norm_eq_zpow_log_mulValuation ((map_ne_zero τ).mpr hx), he]

theorem padicEmbeddingPrime_injective : Function.Injective (PadicEmbeddingMem.Realization.padicEmbeddingPrime q (E := E)) := by
  intro σ τ h
  apply AlgHom.ext
  intro x
  have hnorm : (fun z : ℚ_[q] => ‖σ x - z‖) = (fun z : ℚ_[q] => ‖τ x - z‖) := by
    apply (Padic.denseRange_ratCast q).equalizer
      ((continuous_const.sub continuous_id).norm) ((continuous_const.sub continuous_id).norm)
    funext z
    change ‖σ x - (z : ℚ_[q])‖ = ‖τ x - (z : ℚ_[q])‖
    have hz := padicEmbedding_same_prime_norm q σ τ h (x - algebraMap ℚ E z)
    have hr : algebraMap ℚ ℚ_[q] z = (z : ℚ_[q]) := map_ratCast (algebraMap ℚ ℚ_[q]) z
    simpa only [map_sub, AlgHom.commutes, hr] using hz
  have hz := congrFun hnorm (σ x)
  rw [sub_self, norm_zero] at hz
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz.symm)).symm

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PadicEmbeddingPrimeInjective.Realization
