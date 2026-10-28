import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Embedded Linear Group -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup

noncomputable section

section

/-! An E-linear automorphism induces an actual complex-linear
automorphism in every embedding block. -/

variable {E : Type} [Field E] [Algebra ℚ E]

def embeddedLinearIso (u : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) (τ : E →ₐ[ℚ] ℂ) :
    (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) := by
  have hu : IsUnit (LinearMap.toMatrix' u.toLinearMap).det := by
    simpa only [LinearMap.toMatrix_eq_toMatrix'] using
      u.isUnit_det (Pi.basisFun E (Fin 3)) (Pi.basisFun E (Fin 3))
  have hτ : IsUnit (((LinearMap.toMatrix' u.toLinearMap).map τ).det) :=
    (τ.map_det (LinearMap.toMatrix' u.toLinearMap)) ▸ hu.map τ.toRingHom
  exact ((LinearMap.toMatrix' u.toLinearMap).map τ).toLinearEquiv (Pi.basisFun ℂ (Fin 3)) hτ

theorem embeddedLinearIso_apply (u : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) (τ : E →ₐ[ℚ] ℂ)
    (x : Fin 3 → ℂ) :
    embeddedLinearIso u τ x = ((LinearMap.toMatrix' u.toLinearMap).map τ).mulVec x := rfl

end

/-! Embedding the actual E-linear automorphisms respects their identity
and multiplication as complex-linear automorphisms. -/

variable {E : Type} [Field E] [Algebra ℚ E] (σ : E →ₐ[ℚ] ℂ)

theorem embeddedLinearIso_one : embeddedLinearIso (1 : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) σ = 1 := by
  apply LinearEquiv.ext
  intro x
  change ((LinearMap.toMatrix' (LinearMap.id : (Fin 3 → E) →ₗ[E] (Fin 3 → E))).map σ).mulVec x = x
  simp

theorem embeddedLinearIso_mul (f g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) :
    embeddedLinearIso (f * g) σ = embeddedLinearIso f σ * embeddedLinearIso g σ := by
  apply LinearEquiv.ext
  intro x
  change ((LinearMap.toMatrix' (f.toLinearMap.comp g.toLinearMap)).map σ).mulVec x =
    ((LinearMap.toMatrix' f.toLinearMap).map σ).mulVec (((LinearMap.toMatrix' g.toLinearMap).map σ).mulVec x)
  rw [LinearMap.toMatrix'_comp, Matrix.map_mul, Matrix.mulVec_mulVec]

def embeddedLinearGroup : ((Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) →* ((Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) where
  toFun f := embeddedLinearIso f σ
  map_one' := embeddedLinearIso_one σ
  map_mul' := embeddedLinearIso_mul σ

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup
