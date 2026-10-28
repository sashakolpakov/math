import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Family Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.FamilyFactorization

noncomputable section

/-! A Cartesian family over a composite parameter map factors canonically
through the family over the intermediate parameter scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C]
variable {X S T U P : C} (f : X ⟶ S) (t₁ : U ⟶ S) (t₂ : T ⟶ U)
variable [HasPullback f t₁] {a : P ⟶ X} {b : P ⟶ T}
variable (H : IsPullback a b f (t₂ ≫ t₁))

def cartesianFamilyFactorMap : P ⟶ pullback f t₁ :=
  pullback.lift a (b ≫ t₂) (by simpa only [Category.assoc] using H.w)

theorem cartesianFamilyFactorMap_fst :
    cartesianFamilyFactorMap f t₁ t₂ H ≫ pullback.fst f t₁ = a := pullback.lift_fst _ _ _

theorem cartesianFamilyFactorMap_snd :
    cartesianFamilyFactorMap f t₁ t₂ H ≫ pullback.snd f t₁ = b ≫ t₂ := pullback.lift_snd _ _ _

theorem cartesianFamilyFactorMap_isPullback :
    IsPullback (cartesianFamilyFactorMap f t₁ t₂ H) b (pullback.snd f t₁) t₂ := by
  have H' : IsPullback
      (cartesianFamilyFactorMap f t₁ t₂ H ≫ pullback.fst f t₁) b f (t₂ ≫ t₁) := by
    rw [cartesianFamilyFactorMap_fst]
    exact H
  exact H'.of_right (cartesianFamilyFactorMap_snd f t₁ t₂ H) (IsPullback.of_hasPullback f t₁)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.FamilyFactorization
