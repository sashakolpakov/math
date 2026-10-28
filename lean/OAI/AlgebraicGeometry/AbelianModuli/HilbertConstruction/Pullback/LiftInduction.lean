import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Lift Induction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.LiftInduction

/-! Dependent induction on pairs of morphisms into a pullback square. -/

open _root_.CategoryTheory

universe u v

theorem pullbackLift_induction
    {C : Type u} [Category.{v} C] {W A B Z T : C}
    {l : W ⟶ A} {r : W ⟶ B} {p : A ⟶ Z} {q : B ⟶ Z}
    (H : IsPullback l r p q)
    (Q : ∀ (a : T ⟶ A) (b : T ⟶ B), a ≫ p = b ≫ q → Prop)
    (hQ : ∀ (c : T ⟶ W) (h : (c ≫ l) ≫ p = (c ≫ r) ≫ q),
      Q (c ≫ l) (c ≫ r) h)
    (a : T ⟶ A) (b : T ⟶ B) (h : a ≫ p = b ≫ q) : Q a b h := by
  obtain ⟨c, ha, hb⟩ : ∃ c : T ⟶ W, c ≫ l = a ∧ c ≫ r = b :=
    ⟨H.lift a b h, H.lift_fst a b h, H.lift_snd a b h⟩
  subst a
  subst b
  exact hQ c h

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.LiftInduction
