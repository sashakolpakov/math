import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLocalizedVectors
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionCongruenceCoefficients
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Prime Integral Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrimeIntegralLocalization

noncomputable section

/-! Actual prime localizations of the ring of integers, embedded in the
original number field. Localized input coefficients and their conjugates
belong to every localization at a prime dividing the chosen level.
-/

variable (E : Type*) [Field E] [NumberField E]

omit [NumberField E] in
theorem integralPrimeCompl_nonZeroDivisors
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime] :
    p.primeCompl ≤ nonZeroDivisors (NumberField.RingOfIntegers E) := by
  intro a ha
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro h
  apply (Ideal.mem_primeCompl_iff.mp ha)
  rw [h]
  exact p.zero_mem

def primeIntegralLocalization (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime] :
    Subalgebra (NumberField.RingOfIntegers E) E :=
  Localization.subalgebra.ofField E p.primeCompl (integralPrimeCompl_nonZeroDivisors E p)

instance primeIntegralLocalization_isLocalization
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime] :
    IsLocalization p.primeCompl (primeIntegralLocalization E p) := by
  dsimp only [primeIntegralLocalization]
  exact Localization.subalgebra.isLocalization_ofField E p.primeCompl
    (integralPrimeCompl_nonZeroDivisors E p)

instance primeIntegralLocalization_isLocalRing
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime] :
    IsLocalRing (primeIntegralLocalization E p) :=
  IsLocalization.AtPrime.isLocalRing (primeIntegralLocalization E p) p

theorem integral_mem_primeIntegralLocalization
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime]
    (a : NumberField.RingOfIntegers E) : (a : E) ∈ primeIntegralLocalization E p := by
  change ∃ (x s : NumberField.RingOfIntegers E) (_ : s ∈ p.primeCompl),
    (a : E) = (x : E) * (s : E)⁻¹
  exact ⟨a, 1, p.primeCompl.one_mem, by simp⟩

omit [NumberField E] in
theorem successor_level_not_mem_integralPrime
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime]
    (ℓ : ℕ) (hℓ : (ℓ : NumberField.RingOfIntegers E) ∈ p) :
    ((ℓ + 1 : ℕ) : NumberField.RingOfIntegers E) ∉ p := by
  intro h
  apply p.one_notMem
  have hm := p.sub_mem h hℓ
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left] using hm

theorem successor_level_inverse_mem_primeIntegralLocalization
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime]
    (ℓ : ℕ) (hℓ : (ℓ : NumberField.RingOfIntegers E) ∈ p) :
    (((ℓ + 1 : ℕ) : E)⁻¹) ∈ primeIntegralLocalization E p := by
  change ∃ (a s : NumberField.RingOfIntegers E) (_ : s ∈ p.primeCompl),
    (((ℓ + 1 : ℕ) : E)⁻¹) = (a : E) * (s : E)⁻¹
  refine ⟨1, (ℓ + 1 : ℕ),
    Ideal.mem_primeCompl_iff.mpr (successor_level_not_mem_integralPrime E p ℓ hℓ), ?_⟩
  simp

theorem localized_coefficients_mem_primeIntegralLocalization
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime]
    (ℓ : ℕ) (hℓ : (ℓ : NumberField.RingOfIntegers E) ∈ p)
    (z : NumberField.RingOfIntegers E) {x : E}
    (hx : x ∈ EmbeddedLocalizedVectors.localizedCoefficientRing (ℓ + 1) (z : E)) :
    x ∈ primeIntegralLocalization E p := by
  have hsub : EmbeddedLocalizedVectors.localizedCoefficientRing (ℓ + 1) (z : E) ≤
      (primeIntegralLocalization E p).toSubring := by
    apply Subring.closure_le.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact successor_level_inverse_mem_primeIntegralLocalization E p ℓ hℓ
    · obtain rfl := Set.mem_singleton_iff.mp ha
      exact integral_mem_primeIntegralLocalization E p z
  exact hsub hx

theorem level_mem_primeIntegralLocalization_maximalIdeal
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime]
    (ℓ : ℕ) (hℓ : (ℓ : NumberField.RingOfIntegers E) ∈ p) :
    (ℓ : primeIntegralLocalization E p) ∈ IsLocalRing.maximalIdeal (primeIntegralLocalization E p) := by
  have h := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (primeIntegralLocalization E p) p (ℓ : NumberField.RingOfIntegers E)).mpr hℓ
  simpa only [map_natCast] using h

theorem primeIntegralLocalization_normDenominator_isUnit
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime]
    (ℓ : ℕ) (hℓ : (ℓ : NumberField.RingOfIntegers E) ∈ p)
    (q s t r : primeIntegralLocalization E p) :
    IsUnit (ReflectionCongruenceCoefficients.reflectionNormDenominator (ℓ : primeIntegralLocalization E p) q s t r) :=
  ReflectionCongruenceCoefficients.reflectionNormDenominator_isUnit _ q s t r
    (level_mem_primeIntegralLocalization_maximalIdeal E p ℓ hℓ)

theorem conjugate_localized_coefficients_mem_primeIntegralLocalization
    [NumberField.IsCMField E]
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime]
    (ℓ : ℕ) (hℓ : (ℓ : NumberField.RingOfIntegers E) ∈ p)
    (z : NumberField.RingOfIntegers E) {x : E}
    (hx : x ∈ EmbeddedLocalizedVectors.localizedCoefficientRing (ℓ + 1) (z : E)) :
    NumberField.IsCMField.complexConj E x ∈ primeIntegralLocalization E p := by
  apply localized_coefficients_mem_primeIntegralLocalization E p ℓ hℓ
    (NumberField.IsCMField.ringOfIntegersComplexConj E z)
  have hc := Subring.mem_closure_image_of
    (NumberField.IsCMField.complexConj E).toRingHom hx
  rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  change (NumberField.IsCMField.complexConj E).toRingHom x ∈
    EmbeddedLocalizedVectors.localizedCoefficientRing (ℓ + 1) ((NumberField.IsCMField.complexConj E).toRingHom (z : E))
  simpa only [EmbeddedLocalizedVectors.localizedCoefficientRing, Set.image_pair, map_inv₀, map_natCast] using hc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrimeIntegralLocalization
