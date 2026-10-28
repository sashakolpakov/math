import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Product Map -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductMap.Construction.ProductMapSquares

noncomputable section

/-! Changing one factor of a fiber product is a Cartesian base change
of that factor map, with explicit coordinate identities. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {X Y X' Y' S : C}

def left (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S) (q : X' ⟶ X) (hq : q ≫ f = f') :
    pullback f' g ⟶ pullback f g :=
  pullback.map f' g f g q (𝟙 Y) (𝟙 S) (by simpa using hq.symm) (by simp)

theorem left_first (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S) (q : X' ⟶ X) (hq : q ≫ f = f') :
    left f g f' q hq ≫ pullback.fst f g = pullback.fst f' g ≫ q := pullback.lift_fst _ _ _

theorem left_second (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S) (q : X' ⟶ X) (hq : q ≫ f = f') :
    left f g f' q hq ≫ pullback.snd f g = pullback.snd f' g := by
  simp only [left, pullback.map, pullback.lift_snd, Category.comp_id]

theorem left_isPullback (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S) (q : X' ⟶ X) (hq : q ≫ f = f') :
    IsPullback (pullback.fst f' g) (left f g f' q hq) q (pullback.fst f g) := by
  have ho : IsPullback (pullback.fst f' g) (left f g f' q hq ≫ pullback.snd f g) (q ≫ f) g := by
    rw [left_second, hq]
    exact IsPullback.of_hasPullback f' g
  exact IsPullback.of_bot ho (left_first f g f' q hq).symm (IsPullback.of_hasPullback f g)

def right (f : X ⟶ S) (g : Y ⟶ S) (g' : Y' ⟶ S) (q : Y' ⟶ Y) (hq : q ≫ g = g') :
    pullback f g' ⟶ pullback f g :=
  pullback.map f g' f g (𝟙 X) q (𝟙 S) (by simp) (by simpa using hq.symm)

theorem right_first (f : X ⟶ S) (g : Y ⟶ S) (g' : Y' ⟶ S) (q : Y' ⟶ Y) (hq : q ≫ g = g') :
    right f g g' q hq ≫ pullback.fst f g = pullback.fst f g' := by
  simp only [right, pullback.map, pullback.lift_fst, Category.comp_id]

theorem right_second (f : X ⟶ S) (g : Y ⟶ S) (g' : Y' ⟶ S) (q : Y' ⟶ Y) (hq : q ≫ g = g') :
    right f g g' q hq ≫ pullback.snd f g = pullback.snd f g' ≫ q := pullback.lift_snd _ _ _

theorem right_isPullback (f : X ⟶ S) (g : Y ⟶ S) (g' : Y' ⟶ S) (q : Y' ⟶ Y) (hq : q ≫ g = g') :
    IsPullback (pullback.snd f g') (right f g g' q hq) q (pullback.snd f g) := by
  have ho : IsPullback (pullback.snd f g') (right f g g' q hq ≫ pullback.fst f g) (q ≫ g) f := by
    rw [right_first, hq]
    exact (IsPullback.of_hasPullback f g').flip
  exact IsPullback.of_bot ho (right_second f g g' q hq).symm (IsPullback.of_hasPullback f g).flip

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductMap.Construction.ProductMapSquares
