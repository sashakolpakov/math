import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction
import Mathlib.AlgebraicGeometry.Limits

/-! # Cycle Open Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleOpenSquare.BundleCycles

noncomputable section

/-! Coefficient restriction commutes with an injective point pushforward in an actual cartesian scheme square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pointCycle_comap_map_of_isPullback {Z' Z X' X : Scheme.{0}}
    (k : Z' ⟶ Z) (j' : Z' ⟶ X') (j : Z ⟶ X) (a : X' ⟶ X)
    (h : IsPullback k j' j a) (hk : Function.Injective k) (hj' : Function.Injective j')
    (hj : Function.Injective j) (ha : Function.Injective a) (z : Z →₀ ℚ) :
    Finsupp.comapDomain a (Finsupp.mapDomain j z) ha.injOn =
      Finsupp.mapDomain j' (Finsupp.comapDomain k z hk.injOn) := by
  ext x
  by_cases hx : x ∈ Set.range j'
  · obtain ⟨y, rfl⟩ := hx
    have he : a (j' y) = j (k y) := (congrArg (fun f => f y) h.w).symm
    change Finsupp.mapDomain j z (a (j' y)) = _
    rw [he, Finsupp.mapDomain_apply_of_injective hj, Finsupp.mapDomain_apply_of_injective hj']
    rfl
  · have hr : Set.range j' = a ⁻¹' Set.range j := by
      have ht := Scheme.image_preimage_eq_of_isPullback h Set.univ
      simpa only [Set.preimage_univ, Set.image_univ] using ht
    have hx' : a x ∉ Set.range j := fun hm => hx ((congrArg (fun S => x ∈ S) hr).mpr hm)
    change Finsupp.mapDomain j z (a x) = _
    rw [Finsupp.mapDomain_of_notMem_range _ _ hx', Finsupp.mapDomain_of_notMem_range _ _ hx]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleOpenSquare.BundleCycles
