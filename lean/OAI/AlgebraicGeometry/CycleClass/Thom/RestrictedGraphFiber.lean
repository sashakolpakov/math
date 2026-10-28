import OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction
import Mathlib.SetTheory.Cardinal.NatCard

/-! # Restricted Graph Fiber -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphFiber.Constructions

noncomputable section

/-! Fibers of an actual graph restricted over a base open are the full fibers of its covering map when the intervening target map is injective. -/

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

variable {L T N F : Type*}

def graphFiberEquiv (g : L → T) (j : T → N) (hj : Function.Injective j) (e : L → F)
    (U : Set N) (u : U) (y : T) (hy : j y = u.val) :
    {z : ((j ∘ g) ⁻¹' U) | (GraphBaseRestriction.Constructions.restrictedGraph (j ∘ g) e U z).1 = u} ≃ {s : L | g s = y} where
  toFun z := ⟨z.val.val, hj ((congrArg Subtype.val z.property).trans hy.symm)⟩
  invFun s := ⟨⟨s.val, by
    change j (g s.val) ∈ U
    rw [s.property, hy]
    exact u.property⟩, by
      apply Subtype.ext
      change j (g s.val) = u.val
      rw [s.property, hy]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem graphFiber_card (g : L → T) (j : T → N) (hj : Function.Injective j) (e : L → F)
    (U : Set N) (u : U) (y : T) (hy : j y = u.val) :
    Nat.card {z : ((j ∘ g) ⁻¹' U) | (GraphBaseRestriction.Constructions.restrictedGraph (j ∘ g) e U z).1 = u} =
      Nat.card {s : L | g s = y} := Nat.card_congr (graphFiberEquiv g j hj e U u y hy)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphFiber.Constructions
