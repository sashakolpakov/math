import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionDeterminant
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionCongruenceCoefficients

/-! # Reflection Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ReflectionCoefficients

noncomputable section

/-! Norm and matrix-entry formulas for the original Hermitian reflections.
These identities supply the actual coefficients for local congruence control.
-/

variable {K : Type*} [Field K] (σ : K →+* K)
    (B : (Fin 3 → K) →ₗ[K] (Fin 3 → K) →ₛₗ[σ] K)

theorem hermitian_pairing_perturbed_left (m : K) (w c x : Fin 3 → K) :
    B (w + m • c) x = B w x + m * B c x := by
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem hermitian_pairing_perturbed_right
    (m : K) (hm : σ m = m) (x w c : Fin 3 → K) :
    B x (w + m • c) = B x w + m * B x c := by
  rw [(B x).map_add, (B x).map_smulₛₗ]
  change B x w + σ m * B x c = B x w + m * B x c
  rw [hm]

theorem hermitian_perturbation_norm
    (m : K) (hm : σ m = m) (w c : Fin 3 → K) :
    B (w + m • c) (w + m • c) =
      B w w + m * (B w c + B c w) + m ^ 2 * B c c := by
  have hleft (a : K) (x y : Fin 3 → K) : B (a • x) y = a * B x y := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hermitian_pairing_perturbed_right σ B m hm]
  simp only [map_add, LinearMap.add_apply, hleft]
  ring

theorem hermitian_level_perturbation_norm_factor
    (hB : ∀ x y, B x y = σ (B y x))
    (ℓ : K) (hℓ : σ ℓ = ℓ) (w c : Fin 3 → K) :
    B (w + (ℓ * (B w w) ^ 2) • c) (w + (ℓ * (B w w) ^ 2) • c) =
      B w w * ReflectionCongruenceCoefficients.reflectionNormDenominator ℓ (B w w) (B w c) (B c w) (B c c) := by
  have hm : σ (ℓ * (B w w) ^ 2) = ℓ * (B w w) ^ 2 := by
    rw [map_mul, map_pow, hℓ, (hB w w).symm]
  rw [hermitian_perturbation_norm σ B _ hm]
  exact ReflectionCongruenceCoefficients.perturbed_reflection_norm_factor ℓ (B w w) (B w c) (B c w) (B c c)

theorem twoHermitianReflections_matrix_sub_one
    (v w : Fin 3 → K) (hv : B v v ≠ 0) (hw : B w w ≠ 0) (i j : Fin 3) :
    LinearMap.toMatrix' (ReflectionDeterminant.twoHermitianReflections σ B v w hv hw).toLinearMap i j -
      (1 : Matrix (Fin 3) (Fin 3) K) i j =
      -2 * v i * B (Pi.single j 1) v / B v v -
        2 * w i * B (Pi.single j 1) w / B w w +
        4 * v i * B w v * B (Pi.single j 1) w / (B v v * B w w) := by
  let e : Fin 3 → K := Pi.single j 1
  have hleft (a : K) (x y : Fin 3 → K) : B (a • x) y = a * B x y := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hBsub : B (e - (2 * (B e w / B w w)) • w) v =
      B e v - (2 * (B e w / B w w)) * B w v := by
    simp only [map_sub, LinearMap.sub_apply, hleft]
  have he : e i = (1 : Matrix (Fin 3) (Fin 3) K) i j := by
    simp [e, Pi.single_apply, Matrix.one_apply]
  change (e i - (2 * (B e w / B w w)) * w i -
      (2 * (B (e - (2 * (B e w / B w w)) • w) v / B v v)) * v i) -
      (1 : Matrix (Fin 3) (Fin 3) K) i j =
    -2 * v i * B e v / B v v - 2 * w i * B e w / B w w +
      4 * v i * B w v * B e w / (B v v * B w w)
  rw [hBsub, he]
  field_simp [hv, hw]
  ring

theorem twoHermitianReflections_level_coefficient
    (hB : ∀ x y, B x y = σ (B y x))
    (ℓ : K) (hℓ : σ ℓ = ℓ) (w c : Fin 3 → K) (hw : B w w ≠ 0)
    (hv : B (w + (ℓ * (B w w) ^ 2) • c) (w + (ℓ * (B w w) ^ 2) • c) ≠ 0)
    (i j : Fin 3) :
    let q := B w w
    let m := ℓ * q ^ 2
    let v := w + m • c
    LinearMap.toMatrix' (ReflectionDeterminant.twoHermitianReflections σ B v w hv hw).toLinearMap i j -
      (1 : Matrix (Fin 3) (Fin 3) K) i j =
      ℓ * ReflectionCongruenceCoefficients.forwardReflectionDifferencePolynomial q m (w i) (c i)
        (B (Pi.single j 1) w) (B (Pi.single j 1) c) (B w c) (B c w) (B c c) /
        ReflectionCongruenceCoefficients.reflectionNormDenominator ℓ q (B w c) (B c w) (B c c) := by
  have hm : σ (ℓ * (B w w) ^ 2) = ℓ * (B w w) ^ 2 := by
    rw [map_mul, map_pow, hℓ, (hB w w).symm]
  have hD : ReflectionCongruenceCoefficients.reflectionNormDenominator ℓ (B w w) (B w c) (B c w) (B c c) ≠ 0 := by
    intro h
    apply hv
    rw [hermitian_level_perturbation_norm_factor σ B hB ℓ hℓ w c, h, mul_zero]
  dsimp only
  rw [twoHermitianReflections_matrix_sub_one,
    hermitian_perturbation_norm σ B _ hm w c,
    hermitian_pairing_perturbed_right σ B _ hm (Pi.single j 1) w c,
    hermitian_pairing_perturbed_right σ B _ hm w w c]
  exact ReflectionCongruenceCoefficients.forwardReflectionDifference_eq_level_multiple ℓ (B w w) (w i) (c i)
    (B (Pi.single j 1) w) (B (Pi.single j 1) c) (B w c) (B c w) (B c c) hw hD

theorem reverseTwoHermitianReflections_level_coefficient
    (hB : ∀ x y, B x y = σ (B y x))
    (ℓ : K) (hℓ : σ ℓ = ℓ) (w c : Fin 3 → K) (hw : B w w ≠ 0)
    (hv : B (w + (ℓ * (B w w) ^ 2) • c) (w + (ℓ * (B w w) ^ 2) • c) ≠ 0)
    (i j : Fin 3) :
    let q := B w w
    let m := ℓ * q ^ 2
    let v := w + m • c
    LinearMap.toMatrix' (ReflectionDeterminant.twoHermitianReflections σ B w v hw hv).toLinearMap i j -
      (1 : Matrix (Fin 3) (Fin 3) K) i j =
      ℓ * ReflectionCongruenceCoefficients.reverseReflectionDifferencePolynomial q m (w i) (c i)
        (B (Pi.single j 1) w) (B (Pi.single j 1) c) (B w c) (B c w) (B c c) /
        ReflectionCongruenceCoefficients.reflectionNormDenominator ℓ q (B w c) (B c w) (B c c) := by
  have hm : σ (ℓ * (B w w) ^ 2) = ℓ * (B w w) ^ 2 := by
    rw [map_mul, map_pow, hℓ, (hB w w).symm]
  have hD : ReflectionCongruenceCoefficients.reflectionNormDenominator ℓ (B w w) (B w c) (B c w) (B c c) ≠ 0 := by
    intro h
    apply hv
    rw [hermitian_level_perturbation_norm_factor σ B hB ℓ hℓ w c, h, mul_zero]
  dsimp only
  rw [twoHermitianReflections_matrix_sub_one,
    hermitian_perturbation_norm σ B _ hm w c,
    hermitian_pairing_perturbed_right σ B _ hm (Pi.single j 1) w c,
    hermitian_pairing_perturbed_left σ B _ w c w]
  exact ReflectionCongruenceCoefficients.reverseReflectionDifference_eq_level_multiple ℓ (B w w) (w i) (c i)
    (B (Pi.single j 1) w) (B (Pi.single j 1) c) (B w c) (B c w) (B c c) hw hD

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ReflectionCoefficients
