import Mathlib

/-! # Surjective Representation Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SurjectiveRepresentationDescent.CM

noncomputable section

/-! A representation descends through a surjective linear map once its
kernel is proved invariant. The resulting action is independent of the
chosen linear section and retains the actual intertwining equation. -/

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (Q : V →ₗ[ℂ] W) (s : W →ₗ[ℂ] V) (hs : ∀ w, Q (s w) = w)
  (ρ : G →* (V ≃ₗ[ℂ] V))
  (hk : ∀ g v, Q v = 0 → Q (ρ g v) = 0)

def lift (g : G) : W →ₗ[ℂ] W := Q.comp ((ρ g).toLinearMap.comp s)

include hs hk in
theorem lift_image (g : G) (v : V) : lift Q s ρ g (Q v) = Q (ρ g v) := by
  have h0 : Q (v - s (Q v)) = 0 := by rw [map_sub, hs, sub_self]
  have h := hk g (v - s (Q v)) h0
  rw [map_sub, map_sub] at h
  exact (sub_eq_zero.mp h).symm

include hs in
theorem lift_one (w : W) : lift Q s ρ 1 w = w := by
  change Q (ρ 1 (s w)) = w
  rw [map_one]
  exact hs w

include hs hk in
theorem lift_mul (g h : G) (w : W) :
    lift Q s ρ (g * h) w = lift Q s ρ g (lift Q s ρ h w) := by
  change Q (ρ (g * h) (s w)) = lift Q s ρ g (Q (ρ h (s w)))
  rw [lift_image Q s hs ρ hk, map_mul, LinearEquiv.mul_apply]

def equivalence (g : G) : W ≃ₗ[ℂ] W where
  toLinearMap := lift Q s ρ g
  invFun := lift Q s ρ g⁻¹
  left_inv w := by
    change lift Q s ρ g⁻¹ (lift Q s ρ g w) = w
    rw [← lift_mul Q s hs ρ hk, inv_mul_cancel, lift_one Q s hs ρ]
  right_inv w := by
    change lift Q s ρ g (lift Q s ρ g⁻¹ w) = w
    rw [← lift_mul Q s hs ρ hk, mul_inv_cancel, lift_one Q s hs ρ]

def action : G →* (W ≃ₗ[ℂ] W) where
  toFun := equivalence Q s hs ρ hk
  map_one' := LinearEquiv.ext (lift_one Q s hs ρ)
  map_mul' g h := LinearEquiv.ext (lift_mul Q s hs ρ hk g h)

theorem intertwines (g : G) (v : V) : action Q s hs ρ hk g (Q v) = Q (ρ g v) :=
  lift_image Q s hs ρ hk g v

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SurjectiveRepresentationDescent.CM
