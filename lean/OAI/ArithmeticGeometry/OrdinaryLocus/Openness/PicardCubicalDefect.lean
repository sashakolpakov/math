import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardField
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.Tactic.Abel

/-! # Picard Cubical Defect -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardCubicalDefect.Construction

noncomputable section

/-! The cubical defect of a line-bundle class and its exact vanishing on the three unit faces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k]
variable {A T : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

def picardCubicalDefect (l : PicardEq.Construction.Picard A.left) (a b c : T ⟶ A) : PicardEq.Construction.Picard T.left :=
  PicardPullback.Construction.picardPullback (a * b * c).left l + PicardPullback.Construction.picardPullback a.left l +
    PicardPullback.Construction.picardPullback b.left l + PicardPullback.Construction.picardPullback c.left l -
    PicardPullback.Construction.picardPullback (a * b).left l - PicardPullback.Construction.picardPullback (a * c).left l - PicardPullback.Construction.picardPullback (b * c).left l

theorem picardPullback_one (l : PicardEq.Construction.Picard A.left) :
    PicardPullback.Construction.picardPullback (1 : T ⟶ A).left l = 0 :=
  PicardField.Construction.picardPullback_constant T.hom (MonObj.one (X := A)).left l

theorem picardCubicalDefect_one_left (l : PicardEq.Construction.Picard A.left) (b c : T ⟶ A) :
    picardCubicalDefect l 1 b c = 0 := by
  simp only [picardCubicalDefect, one_mul, picardPullback_one]
  abel

theorem picardCubicalDefect_one_middle (l : PicardEq.Construction.Picard A.left) (a c : T ⟶ A) :
    picardCubicalDefect l a 1 c = 0 := by
  simp only [picardCubicalDefect, one_mul, mul_one, picardPullback_one]
  abel

theorem picardCubicalDefect_one_right (l : PicardEq.Construction.Picard A.left) (a b : T ⟶ A) :
    picardCubicalDefect l a b 1 = 0 := by
  simp only [picardCubicalDefect, mul_one, picardPullback_one]
  abel

omit [IsCommMonObj A] in
theorem picardCubicalDefect_pullback {U : Over (Spec (.of k))}
    (f : U ⟶ T) (l : PicardEq.Construction.Picard A.left) (a b c : T ⟶ A) :
    PicardPullback.Construction.picardPullback f.left (picardCubicalDefect l a b c) =
      picardCubicalDefect l (f ≫ a) (f ≫ b) (f ≫ c) := by
  have h (g : T ⟶ A) : PicardPullback.Construction.picardPullback f.left (PicardPullback.Construction.picardPullback g.left l) =
      PicardPullback.Construction.picardPullback (f ≫ g).left l :=
    (congrArg (fun q : PicardEq.Construction.Picard A.left →+ PicardEq.Construction.Picard U.left ↦ q l) (PicardPullback.Construction.picardPullback_comp f.left g.left)).symm
  simp only [picardCubicalDefect, map_add, map_sub, h, MonObj.comp_mul]

theorem picardCubicalDefect_pullback_zero_of_face {U : Over (Spec (.of k))}
    (f : U ⟶ T) (l : PicardEq.Construction.Picard A.left) (a b c : T ⟶ A)
    (hf : f ≫ a = 1 ∨ f ≫ b = 1 ∨ f ≫ c = 1) :
    PicardPullback.Construction.picardPullback f.left (picardCubicalDefect l a b c) = 0 := by
  rw [picardCubicalDefect_pullback]
  rcases hf with ha | hb | hc
  · rw [ha, picardCubicalDefect_one_left]
  · rw [hb, picardCubicalDefect_one_middle]
  · rw [hc, picardCubicalDefect_one_right]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardCubicalDefect.Construction
