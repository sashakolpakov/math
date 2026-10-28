import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Factored Base Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredBaseRecovery

noncomputable section

/-! Cartesian recovery factors through any intermediate base without losing the pullback property. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C]
variable {P A S D B : C} (q : P ⟶ A) (p : P ⟶ S) (a : A ⟶ B) (b : S ⟶ D) (c : D ⟶ B)
variable [HasPullback a c] (H : IsPullback q p a (b ≫ c))

def factoredBaseRecovery : P ⟶ pullback a c :=
  pullback.lift q (p ≫ b) (H.w.trans (Category.assoc p b c).symm)

theorem factoredBaseRecovery_fst : factoredBaseRecovery q p a b c H ≫ pullback.fst a c = q :=
  pullback.lift_fst _ _ _

theorem factoredBaseRecovery_snd : factoredBaseRecovery q p a b c H ≫ pullback.snd a c = p ≫ b :=
  pullback.lift_snd _ _ _

theorem factoredBaseRecovery_isPullback :
    IsPullback (factoredBaseRecovery q p a b c H) p (pullback.snd a c) b := by
  have h : IsPullback (factoredBaseRecovery q p a b c H ≫ pullback.fst a c) p a (b ≫ c) := by
    rw [factoredBaseRecovery_fst]
    exact H
  exact h.of_right (factoredBaseRecovery_snd q p a b c H) (IsPullback.of_hasPullback a c)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredBaseRecovery
