import Mathlib

/-! # Intrinsic Unique Lift Centralizer -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicUniqueLiftCentralizer.Intrinsic

/-! Uniqueness of a continuous group lift forces it to commute with
every element whose projection centralizes the projected action. -/

theorem unique_lift_commutes
    {G E P : Type*} [Group G] [TopologicalSpace G]
    [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [Group P]
    (π : E →* P) (s : G →ₜ* E)
    (hu : ∀ t : G →ₜ* E, (∀ g, π (t g) = π (s g)) → ∀ g, t g = s g)
    (b : E) (hb : ∀ g, Commute (π b) (π (s g))) (g : G) : Commute b (s g) := by
  let t : G →ₜ* E :=
    { toFun := fun a => b * s a * b⁻¹
      map_one' := by simp
      map_mul' := by intro a c; simp [map_mul,mul_assoc]
      continuous_toFun := (continuous_const.mul s.continuous).mul continuous_const }
  have hp (a : G) : π (t a) = π (s a) := by
    change π (b * s a * b⁻¹) = _
    rw [map_mul,map_mul,map_inv,(hb a).eq,mul_assoc,mul_inv_cancel,mul_one]
  have he := hu t hp g
  change b * s g = s g * b
  have hh := congrArg (fun a : E => a * b) he
  change (b * s g * b⁻¹) * b = (s g) * b at hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicUniqueLiftCentralizer.Intrinsic
