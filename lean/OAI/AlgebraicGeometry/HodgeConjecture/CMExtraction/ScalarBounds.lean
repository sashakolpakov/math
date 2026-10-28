import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting
import OAI.RepresentationTheory.Hecke.RadialDilation.SplitPrimeSupport

/-! # Scalar Bounds -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarBounds.ParameterChoices

noncomputable section

/-! One native scalar supplies both GaloisValuation's normalized splitting and
RadialDilation's compact-place norms and bounded rational matrices away from q. -/

open _root_.NumberField IsDedekindDomain
open OAI.RepresentationTheory.Hecke.RadialDilation.SplitPrimeSupport.Realization
open scoped Classical WithZero _root_.Matrix

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem native_split_embeddings_bijective (hg : D.HasIntegralModelGeometry)
    (hq : D.IsGoodCompletelySplitPrime) (μ : Fin s) :
    Function.Bijective (RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.splitPairingEmbeddings E ℚ_[q]
      (fun i => GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D (i, false))) := by
  have he : RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.splitPairingEmbeddings E ℚ_[q]
      (fun i => GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D (i, false)) = GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D := by
    funext ⟨i, side⟩
    cases side with
    | false => rfl
    | true =>
      ext x
      exact (RingHom.congr_fun (GaloisDiscrete.ParameterChoices.nativeFieldEmbedding_conjugate D hq i false) x).symm
  rw [he]
  refine ⟨GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding_injective D hq, ?_⟩
  intro f
  obtain ⟨i, hi⟩ := (GaloisDiscrete.ParameterChoices.nativeLocalLabel_bijective D hg hq (μ, false)).2
    (GaloisDiscrete.ParameterChoices.embeddingAutEquiv (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (μ, false)) f)
  exact ⟨i, (GaloisDiscrete.ParameterChoices.embeddingAutEquiv (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (μ, false))).injective hi⟩

theorem native_global_splitting_of_local (hg : D.HasIntegralModelGeometry)
    (hq : D.IsGoodCompletelySplitPrime) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    (μ : Fin s) (r : Eˣ) (M : ℕ)
    (hval : ∀ i : Fin s × Bool, (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i (r : E)).valuation =
      if i = (μ, true) then (M : ℤ) else if i = (μ, false) then -(M : ℤ) else 0) :
    ∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (μ, false)) (ιE (τ (r : E))) =
      if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0 := by
  intro τ
  rw [ClosureSplitting.ParameterChoices.nativeGlobalValuation_on_field]
  obtain ⟨i, rfl⟩ := (GaloisDiscrete.ParameterChoices.nativeLocalLabel_bijective D hg hq (μ, false)).2 τ
  rw [GaloisDiscrete.ParameterChoices.nativeLocalLabel_spec, hval]
  have hc : GaloisDiscrete.ParameterChoices.nativeLocalLabel D (μ, false) i = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E ↔ i = (μ, true) := by
    change GaloisDiscrete.ParameterChoices.nativeLocalLabel D (μ, false) i =
      (NumberField.IsCMField.complexConj E).restrictScalars ℚ ↔ _
    rw [← GaloisDiscrete.ParameterChoices.nativeLocalLabel_conjugate D hq μ false]
    exact (GaloisDiscrete.ParameterChoices.nativeLocalLabel_bijective D hg hq (μ, false)).1.eq_iff
  have hid : GaloisDiscrete.ParameterChoices.nativeLocalLabel D (μ, false) i = 1 ↔ i = (μ, false) := by
    rw [← GaloisDiscrete.ParameterChoices.nativeLocalLabel_self D (μ, false)]
    exact (GaloisDiscrete.ParameterChoices.nativeLocalLabel_bijective D hg hq (μ, false)).1.eq_iff
  rw [hc, hid]
  split_ifs <;> simp only [Int.cast_natCast, Int.cast_neg, Int.cast_zero]

theorem exists_native_scalar_with_bounds
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (μ : Fin s) :
    ∃ (r : Eˣ) (M : ℕ), 0 < M ∧ (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
      (∀ i : Fin s × Bool, (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i (r : E)).valuation =
        if i = (μ, true) then (M : ℤ) else if i = (μ, false) then -(M : ℤ) else 0) ∧
      (∀ τ : Gal(E/ℚ),
        NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (μ, false)) (ιE (τ (r : E))) =
          if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
      (∀ i : Fin s, i ≠ μ → ‖LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (i, false) (r : E)‖ = 1) ∧
      ‖(LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (μ, false) (r : E))⁻¹‖ = (q : ℝ) ^ (-(M : ℤ)) ∧
      (∀ p : HeightOneSpectrum (𝓞 E),
        p ≠ Intrinsic.Primes.ParameterChoices.nativeLocalPrime D (μ, true) → p ≠ Intrinsic.Primes.ParameterChoices.nativeLocalPrime D (μ, false) →
          p.valuation E (r : E) = 1) ∧
      (∀ {I : Type*} [Fintype I] [DecidableEq I] (e : (Fin 3 → E) ≃ₗ[ℚ] (I → ℚ)),
        ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ B : ℝ, ∀ (N : ℕ) i j,
          ‖((RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix E e (r : E)).map (algebraMap ℚ ℚ_[p]) ^ N) i j‖ ≤ B) := by
  obtain ⟨r, M, hM, hr, hv, hs, _⟩ := Intrinsic.Primes.ParameterChoices.exists_native_split_scalar D hq μ true
  have hval : ∀ i : Fin s × Bool, (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i (r : E)).valuation =
      if i = (μ, true) then (M : ℤ) else if i = (μ, false) then -(M : ℤ) else 0 := by
    intro i
    apply GaloisDiscrete.ParameterChoices.nativeFieldEmbedding_valuation_of_value D i (r : E) r.ne_zero
    have hi := hv i
    simp only [Bool.not_true] at hi
    split_ifs at hi ⊢ <;> simpa only [neg_neg, neg_zero, WithZero.exp_zero] using hi
  refine ⟨r, M, hM, hr, hval, native_global_splitting_of_local E D hg hq ιE μ r M hval,
    ?_, ?_, hs, ?_⟩
  · intro i hi
    rw [Padic.norm_eq_zpow_neg_valuation ((map_ne_zero _).mpr r.ne_zero), hval]
    simp [hi]
  · rw [norm_inv, Padic.norm_eq_zpow_neg_valuation ((map_ne_zero _).mpr r.ne_zero)]
    simp [hval, zpow_neg]
  · intro I hI hdec e
    exact RepresentationTheory.Hecke.RadialDilation.PadicEmbeddingMem.Realization.rational_scalar_all_away_power_bounds E q
      (Intrinsic.Primes.ParameterChoices.nativeLocalPrime D (μ, true)) (Intrinsic.Primes.ParameterChoices.nativeLocalPrime D (μ, false))
      (Intrinsic.Primes.ParameterChoices.nativeLocalPrime_liesOver D _) (Intrinsic.Primes.ParameterChoices.nativeLocalPrime_liesOver D _) e (r : E) hs

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarBounds.ParameterChoices
