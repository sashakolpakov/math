import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Reflexive Transpose Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflexiveTransposeAction

noncomputable section

/-! A commutative ring action on the dual of a reflexive module induces
the actual transpose action on the module. Its evaluation identity
determines every operator, including over rings with nilpotents. -/

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [Module.IsReflexive R V]

def reflexiveTranspose (f : Module.End R (Module.Dual R V)) : Module.End R V :=
  (Module.evalEquiv R V).symm.toLinearMap.comp
    (f.dualMap.comp (Module.evalEquiv R V).toLinearMap)

theorem reflexiveTranspose_pairing (f : Module.End R (Module.Dual R V))
    (ℓ : Module.Dual R V) (v : V) : ℓ (reflexiveTranspose f v) = (f ℓ) v := by
  change ℓ ((Module.evalEquiv R V).symm (f.dualMap (Module.evalEquiv R V v))) = (f ℓ) v
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

theorem reflexive_eq_of_dual (x y : V) (h : ∀ ℓ : Module.Dual R V, ℓ x = ℓ y) : x = y :=
  (Module.bijective_dual_eval R V).injective (LinearMap.ext h)

def reflexiveTransposeAction {O : Type} [CommRing O]
    (ρ : O →+* Module.End R (Module.Dual R V)) : O →+* Module.End R V where
  toFun a := reflexiveTranspose (ρ a)
  map_zero' := by
    apply LinearMap.ext
    intro v
    apply reflexive_eq_of_dual (R := R)
    intro ℓ
    rw [reflexiveTranspose_pairing, map_zero]
    exact ℓ.map_zero.symm
  map_one' := by
    apply LinearMap.ext
    intro v
    apply reflexive_eq_of_dual (R := R)
    intro ℓ
    rw [reflexiveTranspose_pairing, map_one]
    rfl
  map_add' a b := by
    apply LinearMap.ext
    intro v
    apply reflexive_eq_of_dual (R := R)
    intro ℓ
    change ℓ (reflexiveTranspose (ρ (a + b)) v) =
      ℓ (reflexiveTranspose (ρ a) v + reflexiveTranspose (ρ b) v)
    rw [reflexiveTranspose_pairing, map_add, ℓ.map_add,
      reflexiveTranspose_pairing, reflexiveTranspose_pairing]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    apply reflexive_eq_of_dual (R := R)
    intro ℓ
    change ℓ (reflexiveTranspose (ρ (a * b)) v) =
      ℓ (reflexiveTranspose (ρ a) (reflexiveTranspose (ρ b) v))
    rw [reflexiveTranspose_pairing, reflexiveTranspose_pairing, reflexiveTranspose_pairing]
    rw [mul_comm a b, map_mul]
    rfl

theorem reflexiveTransposeAction_pairing {O : Type} [CommRing O]
    (ρ : O →+* Module.End R (Module.Dual R V)) (a : O) (ℓ : Module.Dual R V) (v : V) :
    ℓ (reflexiveTransposeAction ρ a v) = (ρ a ℓ) v :=
  reflexiveTranspose_pairing (ρ a) ℓ v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflexiveTransposeAction
