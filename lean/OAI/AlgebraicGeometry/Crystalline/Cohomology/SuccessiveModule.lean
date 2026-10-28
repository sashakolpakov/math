import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Group.Commute.Units

/-! # Successive Module -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SuccessiveModule.SuccessiveModuleLocalization

noncomputable section

/-!
# Successive principal localization of modules

If a module is first localized at `b`, and the composite map localizes
at `b * s`, the second map is localization at `s`.
-/

universe u

variable (R M N P : Type u) [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (b s : R) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
  [IsLocalizedModule.Away b f] [IsLocalizedModule.Away (b * s) (g.comp f)]

include b f in
theorem isLocalizedModule : IsLocalizedModule.Away s g := by
  have hu := IsLocalizedModule.Away.isUnit_algebraMap (g.comp f) (b * s)
  rw [map_mul] at hu
  have hc : Commute (algebraMap R (Module.End R P) b)
      (algebraMap R (Module.End R P) s) := (Commute.all b s).map _
  obtain ⟨hb, hs⟩ := hc.isUnit_mul_iff.mp hu
  apply IsLocalizedModule.Away.mk_of_addCommGroup hs
  · intro z
    obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj (g.comp f) (b * s) z
    have hbn := IsLocalizedModule.map_units (S := Submonoid.powers b) f ⟨b ^ n, n, rfl⟩
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).mp hbn).surjective (f x)
    change b ^ n • y = f x at hy
    refine ⟨n, y, ?_⟩
    apply ((Module.End.isUnit_iff _).mp (hb.pow n)).injective
    rw [← map_pow]
    change b ^ n • (s ^ n • z) = b ^ n • g y
    rw [← g.map_smul, hy]
    simpa only [mul_pow, mul_smul, LinearMap.comp_apply] using hx
  · intro y hy
    obtain ⟨k, x, hx⟩ := IsLocalizedModule.Away.surj f b y
    have hfx : (g.comp f) x = (g.comp f) 0 := by
      simp only [LinearMap.comp_apply, ← hx, map_smul, hy, smul_zero, map_zero]
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (b * s) hfx
    have he : b ^ (n + k) • (s ^ n • y) = b ^ (n + k) • (0 : N) := by
      have hm := congrArg f hn
      simp only [map_smul, ← hx, map_zero, smul_zero, mul_pow, mul_smul] at hm
      rw [pow_add, mul_smul, smul_comm (b ^ k) (s ^ n)]
      simpa only [smul_zero] using hm
    have hbn := IsLocalizedModule.map_units (S := Submonoid.powers b) f
      ⟨b ^ (n + k), n + k, rfl⟩
    exact ⟨n, ((Module.End.isUnit_iff _).mp hbn).injective he⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SuccessiveModule.SuccessiveModuleLocalization
