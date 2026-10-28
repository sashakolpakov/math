import OAI.RepresentationTheory.Hecke.RadialDilation.PadicEmbeddingPrimeInjective
import OAI.RepresentationTheory.Hecke.RadialDilation.GeometricSplitScalar

/-! # Split Prime Support -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SplitPrimeSupport.Realization

noncomputable section

section

/-! The valuation support of the CM scalar identifies the active and compact split blocks. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField

theorem splitScalarUnits_apply {F K Place : Type*} [Field F] [Field K] [Algebra ℚ F] [Algebra ℚ K]
    (σ : Place → F →ₐ[ℚ] K) (r : Fˣ) (τ : Place) :
    (GeometricSplitScalar.Realization.splitScalarUnits σ r τ : K) = σ τ (r : F) := rfl

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
variable (q : ℕ) [Fact q.Prime] {Place : Type*} (μ : Place)

theorem split_embedding_prime_conjugation (σ : E →ₐ[ℚ] ℚ_[q]) :
    (PadicEmbeddingMem.Realization.padicEmbeddingPrime q σ).asIdeal =
      Ideal.map (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom
        (PadicEmbeddingMem.Realization.padicEmbeddingPrime q (SplitTrace.Realization.conjugateSplitEmbedding E ℚ_[q] σ)).asIdeal := by
  let c := NumberField.IsCMField.ringOfIntegersComplexConj E
  have he : (PadicEmbeddingMem.Realization.padicEmbeddingPrime q (SplitTrace.Realization.conjugateSplitEmbedding E ℚ_[q] σ)).asIdeal =
      Ideal.comap c.toRingHom (PadicEmbeddingMem.Realization.padicEmbeddingPrime q σ).asIdeal := by
    apply Ideal.ext
    intro x
    rw [PadicEmbeddingMem.Realization.padicEmbeddingPrime_mem]
    change ‖σ (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (x : E))‖ < 1 ↔ c x ∈ (PadicEmbeddingMem.Realization.padicEmbeddingPrime q σ).asIdeal
    rw [PadicEmbeddingMem.Realization.padicEmbeddingPrime_mem]
    rfl
  rw [he]
  exact (Ideal.map_comap_of_surjective c.toRingHom c.surjective _).symm

theorem split_prime_pair_distinct (σ : Place → E →ₐ[ℚ] ℚ_[q])
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E ℚ_[q] σ)) :
    PadicEmbeddingMem.Realization.padicEmbeddingPrime q (SplitTrace.Realization.conjugateSplitEmbedding E ℚ_[q] (σ μ)) ≠ PadicEmbeddingMem.Realization.padicEmbeddingPrime q (σ μ) := by
  intro he
  have h := PadicEmbeddingPrimeInjective.Realization.padicEmbeddingPrime_injective q he
  have hp : (μ, true) = (μ, false) := hσ.injective h
  exact Bool.false_ne_true (congrArg Prod.snd hp).symm

theorem split_scalar_support_norms (σ : Place → E →ₐ[ℚ] ℚ_[q])
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E ℚ_[q] σ)) (r : Eˣ) (M : ℕ)
    (hactive : (PadicEmbeddingMem.Realization.padicEmbeddingPrime q (σ μ)).valuation E (r : E) = WithZero.exp (M : ℤ))
    (hsupport : ∀ w : HeightOneSpectrum (𝓞 E),
      w ≠ PadicEmbeddingMem.Realization.padicEmbeddingPrime q (SplitTrace.Realization.conjugateSplitEmbedding E ℚ_[q] (σ μ)) →
      w ≠ PadicEmbeddingMem.Realization.padicEmbeddingPrime q (σ μ) → w.valuation E (r : E) = 1) :
    (∀ τ, τ ≠ μ → ‖(GeometricSplitScalar.Realization.splitScalarUnits σ r τ : ℚ_[q])‖ = 1) ∧
      ‖((GeometricSplitScalar.Realization.splitScalarUnits σ r μ)⁻¹ : ℚ_[q]ˣ).val‖ = (q : ℝ) ^ (-(M : ℤ)) := by
  constructor
  · intro τ hτ
    have hne₀ : PadicEmbeddingMem.Realization.padicEmbeddingPrime q (σ τ) ≠
        PadicEmbeddingMem.Realization.padicEmbeddingPrime q (SplitTrace.Realization.conjugateSplitEmbedding E ℚ_[q] (σ μ)) := by
      intro he
      have hp : (τ, false) = (μ, true) := hσ.injective (PadicEmbeddingPrimeInjective.Realization.padicEmbeddingPrime_injective q he)
      exact Bool.false_ne_true (congrArg Prod.snd hp)
    have hne₁ : PadicEmbeddingMem.Realization.padicEmbeddingPrime q (σ τ) ≠ PadicEmbeddingMem.Realization.padicEmbeddingPrime q (σ μ) := by
      intro he
      have hp : (τ, false) = (μ, false) := hσ.injective (PadicEmbeddingPrimeInjective.Realization.padicEmbeddingPrime_injective q he)
      exact hτ (congrArg Prod.fst hp)
    have hn := PadicEmbeddingPrimeInjective.Realization.padicEmbedding_norm_of_valuation q (σ τ) (r : E) 0 (hsupport _ hne₀ hne₁)
    rw [splitScalarUnits_apply]
    exact hn.trans (zpow_zero _)
  · have hn := PadicEmbeddingPrimeInjective.Realization.padicEmbedding_norm_of_valuation q (σ μ) (r : E) M hactive
    rw [Units.val_inv_eq_inv_val, norm_inv, splitScalarUnits_apply, hn, zpow_neg]

end

/-! NormOneApproximation supplies the split scalar, its active norm, all compact norms, and all away-prime matrix bounds. -/

open scoped Classical _root_.Matrix
open IsDedekindDomain _root_.NumberField

theorem exists_split_scalar_arithmetic
    (hNormOneApproximation : Prerequisites.Core.NormOneApproximation.Proposition.{0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (q : ℕ) [Fact q.Prime] {Place : Type*} (μ : Place)
    (σ : Place → E →ₐ[ℚ] ℚ_[q])
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E ℚ_[q] σ)) :
    ∃ (r : Eˣ) (M : ℕ), 0 < M ∧
      (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
      (∀ τ, τ ≠ μ → ‖(GeometricSplitScalar.Realization.splitScalarUnits σ r τ : ℚ_[q])‖ = 1) ∧
      ‖((GeometricSplitScalar.Realization.splitScalarUnits σ r μ)⁻¹ : ℚ_[q]ˣ).val‖ = (q : ℝ) ^ (-(M : ℤ)) ∧
      ∀ {I : Type*} [Fintype I] [DecidableEq I] (e : (Fin 3 → E) ≃ₗ[ℚ] (I → ℚ)),
        ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ R : ℝ, ∀ (N : ℕ) i j,
          ‖((RationalCoordinates.Realization.rationalScalarMatrix E e (r : E)).map (algebraMap ℚ ℚ_[p]) ^ N) i j‖ ≤ R := by
  let w₀ := PadicEmbeddingMem.Realization.padicEmbeddingPrime q (SplitTrace.Realization.conjugateSplitEmbedding E ℚ_[q] (σ μ))
  let w₁ := PadicEmbeddingMem.Realization.padicEmbeddingPrime q (σ μ)
  obtain ⟨r, M, hM, hr, _, hv, hs, _⟩ := hNormOneApproximation w₀ w₁
    (split_embedding_prime_conjugation E q (σ μ)) (split_prime_pair_distinct E q μ σ hσ)
  obtain ⟨hcompact, hactive⟩ := split_scalar_support_norms E q μ σ hσ r M hv hs
  refine ⟨r, M, hM, hr, hcompact, hactive, ?_⟩
  intro I hI hdec e
  exact PadicEmbeddingMem.Realization.rational_scalar_all_away_power_bounds E q w₀ w₁
    (PadicEmbeddingMem.Realization.padicEmbeddingPrime_contains_prime q _) (PadicEmbeddingMem.Realization.padicEmbeddingPrime_contains_prime q _) e (r : E) hs

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SplitPrimeSupport.Realization
