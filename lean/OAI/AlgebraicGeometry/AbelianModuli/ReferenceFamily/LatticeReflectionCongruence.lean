import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeCongruenceDepth
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ReflectionCongruence

/-! # Lattice Reflection Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeReflectionCongruence

noncomputable section

/-! The given full integral lattice admits one depth at which the
constructed rational reflections and their inverses have integral
representatives preserving the prescribed principal marking.
-/

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

def ClearedPrincipalLatticeCongruence
    (Λ : Submodule ℤ (Fin 3 → E)) (N : ℕ)
    (g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) : Prop :=
  ∃ D : ℕ, 0 < D ∧ Nat.Coprime D N ∧ (N : ℤ) ∣ (D : ℤ) - 1 ∧
    (∀ x ∈ Λ, ∃ y ∈ Λ, D • g x - x = N • y) ∧
    (∀ x ∈ Λ, ∃ y ∈ Λ, D • g.symm x - x = N • y)

theorem exists_integral_reflection_lattice_depth
    (Λ : Submodule ℤ (Fin 3 → E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (N : ℕ) (hN : 0 < N) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ N ∣ ℓ ∧
      ∀ (H : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E))
        (_hHerm : ∀ i j, (H i j : E) = NumberField.IsCMField.complexConj E (H j i : E))
        (w : Fin 3 → NumberField.RingOfIntegers E)
        (z : NumberField.RingOfIntegers E) (c : Fin 3 → E)
        (_hc : ∀ i, c i ∈ EmbeddedLocalizedVectors.localizedCoefficientRing (ℓ + 1) (z : E))
        (hw : IntegralHermitianCoefficients.integralMatrixReflectionForm E H (fun i => (w i : E)) (fun i => (w i : E)) ≠ 0)
        (hv : IntegralHermitianCoefficients.integralMatrixReflectionForm E H
          ((fun i => (w i : E)) + ((ℓ : E) *
            (IntegralHermitianCoefficients.integralMatrixReflectionForm E H (fun i => (w i : E)) (fun i => (w i : E))) ^ 2) • c)
          ((fun i => (w i : E)) + ((ℓ : E) *
            (IntegralHermitianCoefficients.integralMatrixReflectionForm E H (fun i => (w i : E)) (fun i => (w i : E))) ^ 2) • c) ≠ 0),
        ClearedPrincipalLatticeCongruence Λ N
          (ReflectionDeterminant.twoHermitianReflections (NumberField.IsCMField.complexConj E).toRingHom
            (IntegralHermitianCoefficients.integralMatrixReflectionForm E H)
            ((fun i => (w i : E)) + ((ℓ : E) *
              (IntegralHermitianCoefficients.integralMatrixReflectionForm E H (fun i => (w i : E)) (fun i => (w i : E))) ^ 2) • c)
            (fun i => (w i : E)) hv hw) := by
  obtain ⟨ℓ, hℓ, hNℓ, hdepth⟩ := LatticeCongruenceDepth.exists_lattice_depth_for_integral_matrix_congruence
    Λ hΛ.2.2 hΛ.1 hΛ.2.1 N hN
  refine ⟨ℓ, hℓ, hNℓ, ?_⟩
  intro H hHerm w z c hc hw hv
  obtain ⟨D, hD, hcoprime, hcongr, F, G, hcoeff⟩ :=
    Global.ReflectionCongruence.integral_two_reflections_global_congruence E ℓ H hHerm w z c hc hw hv
  let σ := (NumberField.IsCMField.complexConj E).toRingHom
  let B := IntegralHermitianCoefficients.integralMatrixReflectionForm E H
  let w₀ := fun i => (w i : E)
  let g := ReflectionDeterminant.twoHermitianReflections σ B (w₀ + ((ℓ : E) * (B w₀ w₀) ^ 2) • c) w₀ hv hw
  have hdivZ : (N : ℤ) ∣ (ℓ : ℤ) := by
    obtain ⟨k, hk⟩ := hNℓ
    refine ⟨(k : ℤ), ?_⟩
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℤ)) hk
  have hf : ∀ x ∈ Λ, ∃ y ∈ Λ, D • (g x - x) = N • y := by
    intro x hx
    simpa only [Nat.cast_smul_eq_nsmul, LinearEquiv.coe_coe] using
      hdepth D g.toLinearMap F (fun i j => (hcoeff i j).1) x hx
  have hi : ∀ x ∈ Λ, ∃ y ∈ Λ, D • (g.symm x - x) = N • y := by
    intro x hx
    simpa only [Nat.cast_smul_eq_nsmul, LinearEquiv.coe_coe] using
      hdepth D g.symm.toLinearMap G (fun i j => (hcoeff i j).2) x hx
  refine ⟨D, hD, Nat.Coprime.of_dvd_right hNℓ hcoprime, hdivZ.trans hcongr, ?_, ?_⟩
  · exact MatrixToLatticeCongruence.integer_multiple_congruent_one_on_lattice Λ D N (hdivZ.trans hcongr) g hf
  · exact MatrixToLatticeCongruence.integer_multiple_congruent_one_on_lattice Λ D N (hdivZ.trans hcongr) g.symm hi

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeReflectionCongruence
