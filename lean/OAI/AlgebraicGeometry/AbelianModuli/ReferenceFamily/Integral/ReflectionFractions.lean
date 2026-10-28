import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegralHermitianCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClearedReflectionPolynomials

/-! # Reflection Fractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ReflectionFractions

noncomputable section

/-! The actual forward and reverse reflection matrices have integral
numerators over one integral denominator congruent to one modulo the
level. All coefficients come from the given integral Hermitian matrix
and the original localized perturbation vector.
-/

variable (E : Type*) [Field E] [NumberField E] [NumberField.IsCMField E]

theorem integral_two_reflections_common_fraction
    (ℓ : ℕ)
    (H : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E))
    (hHerm : ∀ i j, (H i j : E) = NumberField.IsCMField.complexConj E (H j i : E))
    (w : Fin 3 → NumberField.RingOfIntegers E)
    (z : NumberField.RingOfIntegers E) (c : Fin 3 → E)
    (hc : ∀ i, c i ∈ EmbeddedLocalizedVectors.localizedCoefficientRing (ℓ + 1) (z : E))
    (hw : IntegralHermitianCoefficients.integralMatrixReflectionForm E H (fun i => (w i : E)) (fun i => (w i : E)) ≠ 0)
    (hv : IntegralHermitianCoefficients.integralMatrixReflectionForm E H
      ((fun i => (w i : E)) + ((ℓ : E) *
        (IntegralHermitianCoefficients.integralMatrixReflectionForm E H (fun i => (w i : E)) (fun i => (w i : E))) ^ 2) • c)
      ((fun i => (w i : E)) + ((ℓ : E) *
        (IntegralHermitianCoefficients.integralMatrixReflectionForm E H (fun i => (w i : E)) (fun i => (w i : E))) ^ 2) • c) ≠ 0) :
    let σ := (NumberField.IsCMField.complexConj E).toRingHom
    let B := IntegralHermitianCoefficients.integralMatrixReflectionForm E H
    let w₀ := fun i => (w i : E)
    let v := w₀ + ((ℓ : E) * (B w₀ w₀) ^ 2) • c
    ∃ A : NumberField.RingOfIntegers E, (A : E) ≠ 0 ∧
      (∃ t : NumberField.RingOfIntegers E, A = 1 + (ℓ : NumberField.RingOfIntegers E) * t) ∧
      ∃ F G : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E),
        ∀ i j,
          LinearMap.toMatrix' (ReflectionDeterminant.twoHermitianReflections σ B v w₀ hv hw).toLinearMap i j -
            (1 : Matrix (Fin 3) (Fin 3) E) i j = (ℓ : E) * (F i j : E) / (A : E) ∧
          LinearMap.toMatrix' (ReflectionDeterminant.twoHermitianReflections σ B w₀ v hw hv).toLinearMap i j -
            (1 : Matrix (Fin 3) (Fin 3) E) i j = (ℓ : E) * (G i j : E) / (A : E) := by
  classical
  dsimp only
  let σ := (NumberField.IsCMField.complexConj E).toRingHom
  let B := IntegralHermitianCoefficients.integralMatrixReflectionForm E H
  let w₀ := fun i => (w i : E)
  have hB : ∀ x y, B x y = σ (B y x) :=
    MatrixReflectionEmbedding.matrixReflectionForm_symmetry σ (NumberField.IsCMField.complexConj_apply_apply E)
      (H.map (algebraMap (NumberField.RingOfIntegers E) E)) hHerm
  have hℓ : σ (ℓ : E) = (ℓ : E) := map_natCast σ ℓ
  obtain ⟨n, C, hC⟩ := IntegralHermitianCoefficients.localized_vector_common_integral_denominator E (ℓ + 1)
    (Nat.succ_pos ℓ) z c hc
  let b : NumberField.RingOfIntegers E := ((ℓ : NumberField.RingOfIntegers E) + 1) ^ n
  have hb : (b : E) = ((ℓ + 1 : ℕ) : E) ^ n := by
    simp only [b, map_pow, map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
  have hb0 : (b : E) ≠ 0 := by
    rw [hb]
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero ℓ))
  have hbσ : σ (b : E) = (b : E) := by rw [hb, map_pow, map_natCast]
  have hCvec : (fun i => (C i : E)) = (b : E) • c := by
    ext i
    change (C i : E) = (b : E) * c i
    rw [hC i, hb]
  let q := IntegralHermitianCoefficients.integralHermitianPairing E H w w
  let s := IntegralHermitianCoefficients.integralHermitianPairing E H w C
  let t := IntegralHermitianCoefficients.integralHermitianPairing E H C w
  let r := IntegralHermitianCoefficients.integralHermitianPairing E H C C
  have hq : (q : E) = B w₀ w₀ := IntegralHermitianCoefficients.integralHermitianPairing_coe E H w w
  have hs : (s : E) = (b : E) * B w₀ c := by
    rw [IntegralHermitianCoefficients.integralHermitianPairing_coe E H w C, hCvec]
    rw [(B w₀).map_smulₛₗ (b : E) c]
    change σ (b : E) * B w₀ c = _
    rw [hbσ]
  have ht : (t : E) = (b : E) * B c w₀ := by
    rw [IntegralHermitianCoefficients.integralHermitianPairing_coe E H C w, hCvec]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rfl
  have hr : (r : E) = (b : E) ^ 2 * B c c := by
    rw [IntegralHermitianCoefficients.integralHermitianPairing_coe E H C C, hCvec]
    rw [B.map_smul (b : E) c, LinearMap.smul_apply, (B c).map_smulₛₗ (b : E) c]
    change (b : E) * (σ (b : E) * B c c) = (b : E) ^ 2 * B c c
    rw [hbσ]
    ring
  let A := ClearedReflectionPolynomials.clearedReflectionNormDenominator (ℓ : NumberField.RingOfIntegers E) b q s t r
  have hA : (A : E) = (b : E) ^ 2 *
      ReflectionCongruenceCoefficients.reflectionNormDenominator (ℓ : E) (B w₀ w₀) (B w₀ c) (B c w₀) (B c c) := by
    change algebraMap (NumberField.RingOfIntegers E) E
      (ClearedReflectionPolynomials.clearedReflectionNormDenominator (ℓ : NumberField.RingOfIntegers E) b q s t r) = _
    simp only [ClearedReflectionPolynomials.clearedReflectionNormDenominator, map_add, map_mul, map_pow, map_natCast]
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    rw [hq, hs, ht, hr]
    exact (ClearedReflectionPolynomials.reflectionNormDenominator_clear (ℓ : E) (b : E)
      (B w₀ w₀) (B w₀ c) (B c w₀) (B c c)).symm
  have hD0 : ReflectionCongruenceCoefficients.reflectionNormDenominator (ℓ : E) (B w₀ w₀) (B w₀ c) (B c w₀) (B c c) ≠ 0 := by
    intro h
    apply hv
    rw [Hermitian.ReflectionCoefficients.hermitian_level_perturbation_norm_factor σ B hB (ℓ : E) hℓ w₀ c, h, mul_zero]
  have hA0 : (A : E) ≠ 0 := by rw [hA]; exact mul_ne_zero (pow_ne_zero 2 hb0) hD0
  obtain ⟨u, hu⟩ := ClearedReflectionPolynomials.clearedReflectionNormDenominator_eq_one_add_level
    (ℓ : NumberField.RingOfIntegers E) q s t r n
  let p (j : Fin 3) := IntegralHermitianCoefficients.integralHermitianPairing E H (Pi.single j 1) w
  let d (j : Fin 3) := IntegralHermitianCoefficients.integralHermitianPairing E H (Pi.single j 1) C
  have he (j : Fin 3) :
      (fun i : Fin 3 => ((Pi.single j 1 : Fin 3 → NumberField.RingOfIntegers E) i : E)) =
      (Pi.single j 1 : Fin 3 → E) := by
    ext i
    by_cases h : i = j <;> simp [h]
  have hp (j : Fin 3) : (p j : E) = B (Pi.single j 1) w₀ := by
    rw [IntegralHermitianCoefficients.integralHermitianPairing_coe E H (Pi.single j 1) w, he j]
  have hd (j : Fin 3) : (d j : E) = (b : E) * B (Pi.single j 1) c := by
    rw [IntegralHermitianCoefficients.integralHermitianPairing_coe E H (Pi.single j 1) C, he j, hCvec]
    rw [(B (Pi.single j 1)).map_smulₛₗ (b : E) c]
    change σ (b : E) * B (Pi.single j 1) c = _
    rw [hbσ]
  let m : NumberField.RingOfIntegers E := (ℓ : NumberField.RingOfIntegers E) * q ^ 2
  let F : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E) :=
    fun i j => ClearedReflectionPolynomials.clearedForwardReflectionPolynomial b q m (w i) (C i) (p j) (d j) s t r
  let G : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E) :=
    fun i j => ClearedReflectionPolynomials.clearedReverseReflectionPolynomial b q m (w i) (C i) (p j) (d j) s t r
  have hF (i j : Fin 3) : (F i j : E) = (b : E) ^ 2 *
      ReflectionCongruenceCoefficients.forwardReflectionDifferencePolynomial (B w₀ w₀) ((ℓ : E) * (B w₀ w₀) ^ 2)
        (w₀ i) (c i) (B (Pi.single j 1) w₀) (B (Pi.single j 1) c)
        (B w₀ c) (B c w₀) (B c c) := by
    change algebraMap (NumberField.RingOfIntegers E) E
      (ClearedReflectionPolynomials.clearedForwardReflectionPolynomial b q m (w i) (C i) (p j) (d j) s t r) = _
    simp only [ClearedReflectionPolynomials.clearedForwardReflectionPolynomial, m, map_mul, map_add, map_sub, map_neg,
      map_pow, map_ofNat, map_natCast]
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    rw [hq, hs, ht, hr, hp j, hd j, hC i, ← hb]
    exact (ClearedReflectionPolynomials.forwardReflectionPolynomial_clear (b : E) (B w₀ w₀)
      ((ℓ : E) * (B w₀ w₀) ^ 2) (w₀ i) (c i) (B (Pi.single j 1) w₀)
      (B (Pi.single j 1) c) (B w₀ c) (B c w₀) (B c c)).symm
  have hG (i j : Fin 3) : (G i j : E) = (b : E) ^ 2 *
      ReflectionCongruenceCoefficients.reverseReflectionDifferencePolynomial (B w₀ w₀) ((ℓ : E) * (B w₀ w₀) ^ 2)
        (w₀ i) (c i) (B (Pi.single j 1) w₀) (B (Pi.single j 1) c)
        (B w₀ c) (B c w₀) (B c c) := by
    change algebraMap (NumberField.RingOfIntegers E) E
      (ClearedReflectionPolynomials.clearedReverseReflectionPolynomial b q m (w i) (C i) (p j) (d j) s t r) = _
    simp only [ClearedReflectionPolynomials.clearedReverseReflectionPolynomial, m, map_mul, map_add, map_sub, map_neg,
      map_pow, map_ofNat, map_natCast]
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    rw [hq, hs, ht, hr, hp j, hd j, hC i, ← hb]
    exact (ClearedReflectionPolynomials.reverseReflectionPolynomial_clear (b : E) (B w₀ w₀)
      ((ℓ : E) * (B w₀ w₀) ^ 2) (w₀ i) (c i) (B (Pi.single j 1) w₀)
      (B (Pi.single j 1) c) (B w₀ c) (B c w₀) (B c c)).symm
  refine ⟨A, hA0, ⟨u, hu⟩, F, G, ?_⟩
  intro i j
  constructor
  · rw [Hermitian.ReflectionCoefficients.twoHermitianReflections_level_coefficient σ B hB (ℓ : E) hℓ w₀ c hw hv,
      hF i j, hA]
    field_simp [hb0, hD0]
  · rw [Hermitian.ReflectionCoefficients.reverseTwoHermitianReflections_level_coefficient σ B hB (ℓ : E) hℓ w₀ c hw hv,
      hG i j, hA]
    field_simp [hb0, hD0]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ReflectionFractions
