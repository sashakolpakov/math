import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
import Mathlib.Algebra.Group.Subgroup.Finite

/-! # Compact Typed Choices -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactTypedChoices

noncomputable section

/-! The original compact elementary types force the entire subgroup
or the identity subgroup. This uses actual finite group cardinalities,
and retains the subgroup itself rather than only its abstract type. -/

theorem compactElementary_card (q m : ℕ) (flag : Bool) :
    Nat.card (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) =
      if flag then (q ^ m) ^ 3 else 1 := by
  cases flag <;>
    simp [AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule, Nat.card_pi, Nat.card_zmod]

variable (q m : ℕ) (G : Type) [AddCommGroup G] [Finite G]
variable (hcard : Nat.card G = (q ^ m) ^ 3)

include hcard in
theorem typed_compact_subgroup_eq (flag : Bool) (J : AddSubgroup G)
    (hJ : Nonempty (J ≃+ AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0))) :
    J = if flag then ⊤ else ⊥ := by
  obtain ⟨e⟩ := hJ
  have hc := (Nat.card_congr e.toEquiv).trans (compactElementary_card q m flag)
  cases flag with
  | false => exact J.eq_bot_of_card_eq hc
  | true => exact J.eq_top_of_card_eq (hc.trans hcard.symm)

include hcard in
theorem typed_compact_subgroups_subsingleton (flag : Bool) :
    Subsingleton {J : AddSubgroup G //
      Nonempty (J ≃+ AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0))} :=
  ⟨fun J K => Subtype.ext ((typed_compact_subgroup_eq q m G hcard flag J.val J.property).trans
    (typed_compact_subgroup_eq q m G hcard flag K.val K.property).symm)⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactTypedChoices
