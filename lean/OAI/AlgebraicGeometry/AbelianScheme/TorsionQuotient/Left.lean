import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Left -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Left.TorsionPullback

/-!
# TorsionQuotient: the actual torsion equalizer is a pullback of multiplication
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] (n : ℕ)

theorem isPullback_over : IsPullback (SubgroupFunctor.torsionι A n) (toUnit (SubgroupFunctor.torsionScheme A n))
    ((𝟙 A : A ⟶ A) ^ n) η[A] := by
  apply IsPullback.mk'
  · have h := equalizer.condition ((𝟙 A : A ⟶ A) ^ n) (1 : A ⟶ A)
    change SubgroupFunctor.torsionι A n ≫ (𝟙 A : A ⟶ A) ^ n = SubgroupFunctor.torsionι A n ≫ (1 : A ⟶ A) at h
    exact h.trans (MonObj.comp_one _)
  · intro T a b hab _
    exact equalizer.hom_ext hab
  · intro T a b hab
    have hb : b ≫ η[A] = (1 : T ⟶ A) := by
      change b ≫ η[A] = toUnit T ≫ η[A]
      exact congrArg (fun z => z ≫ η[A]) (toUnit_unique b (toUnit T))
    have ha : a ^ n = 1 := by
      have h := hab.trans hb
      simpa only [MonObj.comp_pow, Category.comp_id] using h
    exact ⟨SubgroupFunctor.torsionLift n a ha, SubgroupFunctor.torsionLift_ι n a ha, toUnit_unique _ _⟩

/-- Forgetting the base preserves this pullback, so its second projection
is exactly the structural morphism of the actual torsion scheme. -/
theorem isPullback_left : IsPullback (SubgroupFunctor.torsionι A n).left (SubgroupFunctor.torsionScheme A n).hom
    (((𝟙 A : A ⟶ A) ^ n).left) η[A].left :=
  (isPullback_over A n).map (Over.forget S)

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Left.TorsionPullback
