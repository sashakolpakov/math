import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixReflectionEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionScaling
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.CoefficientClearing

/-! # Matrix Form Scaling -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixFormScaling

noncomputable section

/-! Clearing the original Hermitian matrix gives a literal scalar
multiple of its pairing. Consequently its constructed reflections are
unchanged, including their action on arbitrary complex vectors after
the already proved matrix embedding comparison.
-/

variable {E : Type*} [Field E]

theorem matrixReflectionForm_smul (σ : E →+* E) (a : E)
    (H : Matrix (Fin 3) (Fin 3) E) :
    MatrixReflectionEmbedding.matrixReflectionForm σ (a • H) = a • MatrixReflectionEmbedding.matrixReflectionForm σ H := by
  change Matrix.toLinearMapₛₗ₂' E (RingHom.id E) σ (a • H) =
    a • Matrix.toLinearMapₛₗ₂' E (RingHom.id E) σ H
  exact (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) σ).map_smul a H

theorem integral_matrix_pairing_eq_scalar_multiple [NumberField E]
    (σ : E →+* E) (d : ℤ) (H : Matrix (Fin 3) (Fin 3) E)
    (H₀ : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E))
    (hH₀ : ∀ i j, (H₀ i j : E) = (d : E) * H i j) :
    MatrixReflectionEmbedding.matrixReflectionForm σ (H₀.map (algebraMap (NumberField.RingOfIntegers E) E)) =
      (d : E) • MatrixReflectionEmbedding.matrixReflectionForm σ H := by
  have he : H₀.map (algebraMap (NumberField.RingOfIntegers E) E) = (d : E) • H := by
    ext i j
    exact hH₀ i j
  rw [he, matrixReflectionForm_smul]

theorem matrixReflectionForm_map_smul
    {K : Type*} [Field K] (τ : K →+* K) (μ : E →+* K)
    (a : E) (H : Matrix (Fin 3) (Fin 3) E) :
    MatrixReflectionEmbedding.matrixReflectionForm τ ((a • H).map μ) =
      μ a • MatrixReflectionEmbedding.matrixReflectionForm τ (H.map μ) := by
  have he : (a • H).map μ = μ a • H.map μ := by
    ext i j
    exact map_mul μ a (H i j)
  rw [he, matrixReflectionForm_smul]

theorem integral_matrix_clearing_preserves_hermitian [NumberField E]
    (σ : E →+* E) (d : ℤ) (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = σ (H j i))
    (H₀ : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E))
    (hH₀ : ∀ i j, (H₀ i j : E) = (d : E) * H i j) :
    ∀ i j, (H₀ i j : E) = σ (H₀ j i : E) := by
  intro i j
  rw [hH₀ i j, hH₀ j i, map_mul, map_intCast, hH i j]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixFormScaling
