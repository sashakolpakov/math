import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactTypedChoices
import Mathlib.Algebra.Group.ULift

/-! # Compact Choice Existence -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChoiceExistence

noncomputable section

/-! A constructed rank-three coordinate equivalence supplies the
compact subgroup of the original elementary type. Together with the
cardinality argument this proves existence and uniqueness, preserving
the entire subgroup or the identity subgroup as appropriate. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactTypedChoices

variable (q m : ℕ) [NeZero q] (G : Type) [AddCommGroup G]
  (e : G ≃+ (Fin 3 → ZMod (q ^ m)))

def compactTypedChoice (flag : Bool) :
    {J : AddSubgroup G //
      Nonempty (J ≃+ AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0))} := by
  cases flag with
  | false =>
    refine ⟨⊥, ⟨?_⟩⟩
    change (⊥ : AddSubgroup G) ≃+ ULift (Fin 3 → ZMod 1)
    let : Unique (ULift (Fin 3 → ZMod 1)) := Unique.mk' _
    exact AddEquiv.ofUnique
  | true =>
    exact ⟨⊤, ⟨AddSubgroup.topEquiv.trans (e.trans AddEquiv.ulift.symm)⟩⟩

omit [NeZero q] in
theorem compactTypedChoice_subgroup (flag : Bool) :
    (compactTypedChoice q m G e flag).val = if flag then ⊤ else ⊥ := by
  cases flag <;> rfl

include e in
theorem compactTypedChoice_unique (flag : Bool)
    (J : {J : AddSubgroup G //
      Nonempty (J ≃+ AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0))}) :
    J = compactTypedChoice q m G e flag := by
  have : Finite G := Finite.of_equiv (Fin 3 → ZMod (q ^ m)) e.symm.toEquiv
  have hc : Nat.card G = (q ^ m) ^ 3 := by
    simpa only [Nat.card_pi, Nat.card_zmod, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using Nat.card_congr e.toEquiv
  apply Subtype.ext
  exact (CompactTypedChoices.typed_compact_subgroup_eq q m G hc flag J.val J.property).trans
    (compactTypedChoice_subgroup q m G e flag).symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChoiceExistence
