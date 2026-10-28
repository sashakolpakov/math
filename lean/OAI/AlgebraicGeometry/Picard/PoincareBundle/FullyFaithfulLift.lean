import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Fully Faithful Lift -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FullyFaithfulLift

noncomputable section

/-!
# Lift morphisms through a full functor and a specified recovery isomorphism
-/

open _root_.CategoryTheory

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.Full]
  {A B : C} {X : D} (e : F.obj B ≅ X) (a : F.obj A ⟶ X)

/-- Lift a morphism through the specified presentation of its target. -/
def lift : A ⟶ B := F.preimage (a ≫ e.inv)

/-- The chosen lift recovers the exact original morphism. -/
theorem lift_fac : F.map (lift F e a) ≫ e.hom = a := by
  rw [lift, F.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Faithfulness makes this lift unique. -/
theorem lift_unique [F.Faithful] (b : A ⟶ B) (h : F.map b ≫ e.hom = a) : b = lift F e a := by
  apply F.map_injective
  apply (cancel_mono e.hom).mp
  exact h.trans (lift_fac F e a).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FullyFaithfulLift
