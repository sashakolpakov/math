import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

/-! # Fiber Degree -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.FiberDegree

noncomputable section

/-! Restricting to an open target preserves fiber points and every
native residue-degree weight. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens)

theorem degree (x : (f ⁻¹ᵁ U).toScheme) : (f ∣_ U).residueDegree x = f.residueDegree x.val := by
  rw [← Support.Map.residueDegree_post_immersion (f ∣_ U) U.ι x, morphismRestrict_ι,
    Support.Map.residueDegree_pre_immersion]
  rfl

theorem point (x : (f ⁻¹ᵁ U).toScheme) : ((f ∣_ U) x).val = f x.val := by
  exact congrArg (fun g : (f ⁻¹ᵁ U).toScheme ⟶ Y => g x) (morphismRestrict_ι f U)

def equiv (y : U.toScheme) : (f ∣_ U) ⁻¹' ({y} : Set U.toScheme) ≃ f ⁻¹' ({y.val} : Set Y) where
  toFun x := ⟨x.val.val, (point f U x.val).symm.trans
    (congrArg Subtype.val (show (f ∣_ U) x.val = y from x.property))⟩
  invFun x := ⟨⟨x.val, by change f x.val ∈ U; rw [show f x.val = y.val from x.property]; exact y.property⟩,
    Subtype.ext ((point f U _).trans (show f x.val = y.val from x.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum (y : U.toScheme) [Fintype ((f ∣_ U) ⁻¹' ({y} : Set U.toScheme))]
    [Fintype (f ⁻¹' ({y.val} : Set Y))] :
    ∑ x : (f ∣_ U) ⁻¹' ({y} : Set U.toScheme), (f ∣_ U).residueDegree x.val =
      ∑ x : f ⁻¹' ({y.val} : Set Y), f.residueDegree x.val := by
  rw [← (equiv f U y).sum_comp (fun x => f.residueDegree x.val)]
  exact Finset.sum_congr rfl (fun x _ => degree f U x.val)

theorem generic_degree [IsIntegral X] [Nonempty (f ⁻¹ᵁ U)] :
    (f ∣_ U).residueDegree (genericPoint (f ⁻¹ᵁ U).toScheme) = f.residueDegree (genericPoint X) := by
  rw [degree]
  exact congrArg f.residueDegree (genericPoint_eq_of_isOpenImmersion (f ⁻¹ᵁ U).ι)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.FiberDegree
