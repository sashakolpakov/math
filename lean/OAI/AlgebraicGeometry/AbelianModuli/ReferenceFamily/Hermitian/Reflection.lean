import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LinearReflection
import Mathlib.Tactic.FieldSimp

/-! # Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reflection

noncomputable section

/-! A reflection constructed from a nonisotropic vector preserves the
actual sesquilinear Hermitian pairing. No isometry is an input. -/

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (σ : k →+* k) (B : V →ₗ[k] V →ₛₗ[σ] k)

def hermitianReflectionFunctional (v : V) : V →ₗ[k] k where
  toFun x := B x v / B v v
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, add_div]
  map_smul' a x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_div_assoc]

theorem hermitianReflectionFunctional_normalized (v : V) (hv : B v v ≠ 0) :
    hermitianReflectionFunctional σ B v v = 1 := div_self hv

theorem linearReflectionMap_preserves_hermitian
    (hB : ∀ x y, B x y = σ (B y x))
    (ℓ : V →ₗ[k] k) (v : V) (hℓ : ∀ x, B x v = B v v * ℓ x) (x y : V) :
    B (LinearReflection.linearReflectionMap ℓ v x) (LinearReflection.linearReflectionMap ℓ v y) = B x y := by
  have hleft (a : k) (z : V) : B (a • v) z = a * B v z := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hright (z : V) (a : k) : B z (a • v) = σ a * B z v :=
    (B z).map_smul' a v
  have hq : σ (B v v) = B v v := (hB v v).symm
  change B (x - (2 * ℓ x) • v) (y - (2 * ℓ y) • v) = B x y
  simp only [map_sub, LinearMap.sub_apply, hleft, hright]
  rw [hB v y, hℓ x, hℓ y]
  simp only [map_mul, map_ofNat, hq]
  ring

def hermitianReflection (v : V) (hv : B v v ≠ 0) : V ≃ₗ[k] V :=
  LinearReflection.linearReflectionEquiv (hermitianReflectionFunctional σ B v) v
    (hermitianReflectionFunctional_normalized σ B v hv)

theorem hermitianReflection_preserves
    (hB : ∀ x y, B x y = σ (B y x)) (v : V) (hv : B v v ≠ 0) (x y : V) :
    B (hermitianReflection σ B v hv x) (hermitianReflection σ B v hv y) = B x y := by
  apply linearReflectionMap_preserves_hermitian σ B hB
  intro z
  change B z v = B v v * (B z v / B v v)
  field_simp [hv]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reflection
