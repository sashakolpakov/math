import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.ReflectionCongruence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrimeIntegralLocalization

/-! # Integral Hermitian Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegralHermitianCoefficients

noncomputable section

section

/-! The actual number-field reflection matrices satisfy principal
congruences at every prime of the ring of integers dividing the chosen
level. Integral input data and the explicit localized coefficient ring
supply all local coefficient and relative-norm denominator conditions.
-/

variable (E : Type*) [Field E] [NumberField E] [NumberField.IsCMField E]

def integralMatrixReflectionForm
    (H : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E)) :
    (Fin 3 → E) →ₗ[E] (Fin 3 → E) →ₛₗ[(NumberField.IsCMField.complexConj E).toRingHom] E :=
  MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom
    (H.map (algebraMap (NumberField.RingOfIntegers E) E))

theorem two_integral_matrix_reflections_congruent_at_bad_prime
    (p : Ideal (NumberField.RingOfIntegers E)) [p.IsPrime]
    (ℓ : ℕ) (hℓ : (ℓ : NumberField.RingOfIntegers E) ∈ p)
    (H : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E))
    (hHerm : ∀ i j, (H i j : E) = NumberField.IsCMField.complexConj E (H j i : E))
    (w : Fin 3 → NumberField.RingOfIntegers E)
    (z : NumberField.RingOfIntegers E) (c : Fin 3 → E)
    (hc : ∀ i, c i ∈ EmbeddedLocalizedVectors.localizedCoefficientRing (ℓ + 1) (z : E))
    (hw : integralMatrixReflectionForm E H (fun i => (w i : E)) (fun i => (w i : E)) ≠ 0)
    (hv : integralMatrixReflectionForm E H
      ((fun i => (w i : E)) + ((ℓ : E) *
        (integralMatrixReflectionForm E H (fun i => (w i : E)) (fun i => (w i : E))) ^ 2) • c)
      ((fun i => (w i : E)) + ((ℓ : E) *
        (integralMatrixReflectionForm E H (fun i => (w i : E)) (fun i => (w i : E))) ^ 2) • c) ≠ 0) :
    let σ := (NumberField.IsCMField.complexConj E).toRingHom
    let B := integralMatrixReflectionForm E H
    let w₀ := fun i => (w i : E)
    let v := w₀ + ((ℓ : E) * (B w₀ w₀) ^ 2) • c
    ∀ i j : Fin 3, ∃ a b : PrimeIntegralLocalization.primeIntegralLocalization E p,
      LinearMap.toMatrix' (ReflectionDeterminant.twoHermitianReflections σ B v w₀ hv hw).toLinearMap i j -
        (1 : Matrix (Fin 3) (Fin 3) E) i j = (ℓ : E) * (a : E) ∧
      LinearMap.toMatrix' (ReflectionDeterminant.twoHermitianReflections σ B w₀ v hw hv).toLinearMap i j -
        (1 : Matrix (Fin 3) (Fin 3) E) i j = (ℓ : E) * (b : E) := by
  classical
  dsimp only
  let S : Subring E := (PrimeIntegralLocalization.primeIntegralLocalization E p).toSubring
  let : IsLocalRing S := PrimeIntegralLocalization.primeIntegralLocalization_isLocalRing E p
  let σ := (NumberField.IsCMField.complexConj E).toRingHom
  let H₀ := H.map (algebraMap (NumberField.RingOfIntegers E) E)
  let w₀ := fun i => (w i : E)
  have hσ : Function.Involutive σ := NumberField.IsCMField.complexConj_apply_apply E
  have hH₀ : ∀ i j, H₀ i j = σ (H₀ j i) := hHerm
  have hHS : ∀ i j, H₀ i j ∈ S := fun i j => PrimeIntegralLocalization.integral_mem_primeIntegralLocalization E p (H i j)
  have hwS : ∀ i, w₀ i ∈ S := fun i => PrimeIntegralLocalization.integral_mem_primeIntegralLocalization E p (w i)
  have hwσS : ∀ i, σ (w₀ i) ∈ S := fun i =>
    PrimeIntegralLocalization.integral_mem_primeIntegralLocalization E p (NumberField.IsCMField.ringOfIntegersComplexConj E (w i))
  have hcS : ∀ i, c i ∈ S := fun i =>
    PrimeIntegralLocalization.localized_coefficients_mem_primeIntegralLocalization E p ℓ hℓ z (hc i)
  have hcσS : ∀ i, σ (c i) ∈ S := fun i =>
    PrimeIntegralLocalization.conjugate_localized_coefficients_mem_primeIntegralLocalization E p ℓ hℓ z (hc i)
  have hlevel : (ℓ : S) ∈ IsLocalRing.maximalIdeal S :=
    PrimeIntegralLocalization.level_mem_primeIntegralLocalization_maximalIdeal E p ℓ hℓ
  have hfixed : σ ((ℓ : S) : E) = ((ℓ : S) : E) := map_natCast σ ℓ
  exact Local.ReflectionCongruence.twoMatrixReflections_local_congruence S σ hσ H₀ hH₀ hHS (ℓ : S) hlevel hfixed
    w₀ c hwS hwσS hcS hcσS hw hv

end

/-! Integral representatives for the actual matrix pairing, together
with a common power denominator for localized perturbation coordinates.
Conjugation is performed in the original ring of integers.
-/

variable (E : Type*) [Field E] [NumberField E] [NumberField.IsCMField E]

def integralHermitianPairing
    (H : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E))
    (x y : Fin 3 → NumberField.RingOfIntegers E) : NumberField.RingOfIntegers E :=
  ∑ i, ∑ j, x i * H i j * NumberField.IsCMField.ringOfIntegersComplexConj E (y j)

theorem integralHermitianPairing_coe
    (H : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E))
    (x y : Fin 3 → NumberField.RingOfIntegers E) :
    (integralHermitianPairing E H x y : E) =
      integralMatrixReflectionForm E H (fun i => (x i : E)) (fun i => (y i : E)) := by
  change algebraMap (NumberField.RingOfIntegers E) E
    (∑ i, ∑ j, x i * H i j * NumberField.IsCMField.ringOfIntegersComplexConj E (y j)) = _
  simp only [map_sum, map_mul, integralMatrixReflectionForm, MatrixReflectionEmbedding.matrixReflectionForm_apply,
    Matrix.map_apply, NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  rfl

omit [NumberField.IsCMField E] in
theorem localized_vector_common_integral_denominator
    {I : Type*} [Fintype I] (b : ℕ) (hb : 0 < b)
    (z : NumberField.RingOfIntegers E) (c : I → E)
    (hc : ∀ i, c i ∈ EmbeddedLocalizedVectors.localizedCoefficientRing b (z : E)) :
    ∃ (n : ℕ) (C : I → NumberField.RingOfIntegers E),
      ∀ i, (C i : E) = (b : E) ^ n * c i := by
  let S : Subring E := (integralClosure ℤ E).toSubring
  have hb0 : (b : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)
  obtain ⟨n, hn⟩ := LocalizedCoefficientDenominators.exists_common_power_mul_mem_of_localized_closure S
    (b : E) (z : E) (natCast_mem S b) hb0 z.property c hc
  exact ⟨n, fun i => ⟨(b : E) ^ n * c i, hn i⟩, fun i => rfl⟩

theorem common_integral_denominator_conjugate
    {I : Type*} (b : ℕ) (n : ℕ)
    (c : I → E) (C : I → NumberField.RingOfIntegers E)
    (hC : ∀ i, (C i : E) = (b : E) ^ n * c i) (i : I) :
    (NumberField.IsCMField.ringOfIntegersComplexConj E (C i) : E) =
      (b : E) ^ n * NumberField.IsCMField.complexConj E (c i) := by
  rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj, hC i, map_mul, map_pow,
    map_natCast]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegralHermitianCoefficients
