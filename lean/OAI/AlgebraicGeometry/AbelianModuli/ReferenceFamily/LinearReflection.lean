import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Linear Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LinearReflection

noncomputable section

/-! The rank-one reflection associated to a normalized linear functional
is an actual linear involution. This is the linear-algebra part of the
Hermitian reflection construction. -/

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

def linearReflectionMap (ℓ : V →ₗ[k] k) (v : V) : V →ₗ[k] V where
  toFun x := x - (2 * ℓ x) • v
  map_add' x y := by
    simp only [map_add, mul_add, add_smul]
    abel
  map_smul' a x := by
    simp only [map_smul, smul_eq_mul, smul_sub, smul_smul, RingHom.id_apply]
    rw [show (2 : k) * (a * ℓ x) = a * (2 * ℓ x) by ring]

theorem linearReflectionMap_eval (ℓ : V →ₗ[k] k) (v : V)
    (h : ℓ v = 1) (x : V) :
    ℓ (linearReflectionMap ℓ v x) = -ℓ x := by
  change ℓ (x - (2 * ℓ x) • v) = -ℓ x
  simp only [map_sub, map_smul, h, smul_eq_mul, mul_one]
  ring

theorem linearReflectionMap_involutive (ℓ : V →ₗ[k] k) (v : V)
    (h : ℓ v = 1) : Function.Involutive (linearReflectionMap ℓ v) := by
  intro x
  change (x - (2 * ℓ x) • v) -
    (2 * ℓ (linearReflectionMap ℓ v x)) • v = x
  rw [linearReflectionMap_eval ℓ v h]
  simp only [mul_neg, neg_smul, sub_neg_eq_add]
  abel

def linearReflectionEquiv (ℓ : V →ₗ[k] k) (v : V)
    (h : ℓ v = 1) : V ≃ₗ[k] V :=
  LinearEquiv.ofBijective (linearReflectionMap ℓ v)
    ⟨fun x y hxy => (linearReflectionMap_involutive ℓ v h x).symm.trans
      ((congrArg (linearReflectionMap ℓ v) hxy).trans
        (linearReflectionMap_involutive ℓ v h y)),
      fun x => ⟨linearReflectionMap ℓ v x, linearReflectionMap_involutive ℓ v h x⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LinearReflection
