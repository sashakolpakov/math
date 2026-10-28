import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Fintype.Card

/-! # Finite Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteSubgroup.FiniteSubgroupRanges

/-! An injective marking contained in a subgroup of the same finite type exhausts it. -/

universe u v

theorem range_eq_of_type {M : Type u} {N : Type v} [Group M] [Finite M] [Group N]
    (a : M →* N) (ha : Function.Injective a) (G : Subgroup N)
    (hG : ∀ m, a m ∈ G) (e : G ≃* M) : a.range = G := by
  let f : M → G := fun m => ⟨a m, hG m⟩
  have hi : Function.Injective (fun m => e (f m)) := by
    intro x y h
    exact ha (congrArg Subtype.val (e.injective h))
  have hs := Finite.surjective_of_injective hi
  apply Subgroup.ext
  intro n
  constructor
  · rintro ⟨m, rfl⟩
    exact hG m
  · intro hn
    obtain ⟨m, hm⟩ := hs (e ⟨n, hn⟩)
    exact ⟨m, congrArg Subtype.val (e.injective hm)⟩

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteSubgroup.FiniteSubgroupRanges
