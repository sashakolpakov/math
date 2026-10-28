import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ReflectionFractions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.LevelFractions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionDeterminant

/-! # Reflection Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ReflectionCongruence

noncomputable section

/-! A common positive rational integer, coprime and congruent to one
modulo the level, clears the actual reflection product and its inverse.
Their matrix differences remain literal level multiples of integral
matrices after that common denominator is cleared.
-/

variable (E : Type*) [Field E] [NumberField E] [NumberField.IsCMField E]

theorem integral_two_reflections_global_congruence
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
    let g := ReflectionDeterminant.twoHermitianReflections σ B v w₀ hv hw
    ∃ D : ℕ, 0 < D ∧ Nat.Coprime D ℓ ∧ (ℓ : ℤ) ∣ (D : ℤ) - 1 ∧
      ∃ F G : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E),
        ∀ i j,
          (D : E) * (LinearMap.toMatrix' g.toLinearMap i j -
            (1 : Matrix (Fin 3) (Fin 3) E) i j) = (ℓ : E) * (F i j : E) ∧
          (D : E) * (LinearMap.toMatrix' g.symm.toLinearMap i j -
            (1 : Matrix (Fin 3) (Fin 3) E) i j) = (ℓ : E) * (G i j : E) := by
  classical
  dsimp only
  obtain ⟨A, hA0, ⟨t, rfl⟩, F, G, hcoeff⟩ :=
    Integral.ReflectionFractions.integral_two_reflections_common_fraction E ℓ H hHerm w z c hc hw hv
  have ht0 : (1 + (ℓ : NumberField.RingOfIntegers E) * t) ≠ 0 := by
    intro h
    apply hA0
    exact congrArg (fun a : NumberField.RingOfIntegers E => (a : E)) h
  let P : Bool × Fin 3 × Fin 3 → NumberField.RingOfIntegers E :=
    fun k => if k.1 then F k.2.1 k.2.2 else G k.2.1 k.2.2
  obtain ⟨D, hD, hcoprime, hcongr, R, hR⟩ :=
    LevelFractions.integral_level_fractions_common_denominator E ℓ t ht0 P
  refine ⟨D, hD, hcoprime, hcongr,
    (fun i j => R (true, i, j)), (fun i j => R (false, i, j)), ?_⟩
  intro i j
  constructor
  · rw [(hcoeff i j).1]
    exact hR (true, i, j)
  · rw [ReflectionDeterminant.twoHermitianReflections_symm, (hcoeff i j).2]
    exact hR (false, i, j)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ReflectionCongruence
