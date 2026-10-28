import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Algebra.Ring.Equiv

/-! # Regular Ring Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.RegularRingEquiv.BundleCycles

noncomputable section

/-! Regular elements and their principal ideals transport through
actual coefficient-ring isomorphisms. -/

theorem regular_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (t : R) (ht : IsRegular t) : IsRegular (e t) := by
  have hl : IsLeftRegular (e t) := by
    intro a b h
    apply e.symm.injective
    have he := congrArg e.symm h
    rw [map_mul, map_mul, e.symm_apply_apply] at he
    exact ht.left he
  exact ⟨hl, fun a b h => hl ((mul_comm _ _).trans (h.trans (mul_comm _ _)))⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.RegularRingEquiv.BundleCycles
