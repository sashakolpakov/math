import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Comparison Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ComparisonIsomorphism

noncomputable section

/-! A map commuting with both projections of two pullback squares is an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

theorem isIso_comparison_of_pullbacks
    {C : Type u} [Category.{v} C] {P Q A B Z : C}
    (p₁ : P ⟶ A) (p₂ : P ⟶ B) (q₁ : Q ⟶ A) (q₂ : Q ⟶ B)
    (f : A ⟶ Z) (g : B ⟶ Z) (hP : IsPullback p₁ p₂ f g) (hQ : IsPullback q₁ q₂ f g)
    (c : P ⟶ Q) (hc₁ : c ≫ q₁ = p₁) (hc₂ : c ≫ q₂ = p₂) : IsIso c := by
  have : HasPullback f g := hP.hasPullback
  have he : c = hP.isoPullback.hom ≫ hQ.isoPullback.inv := by
    apply hQ.hom_ext
    · rw [Category.assoc, hQ.isoPullback_inv_fst, hP.isoPullback_hom_fst]
      exact hc₁
    · rw [Category.assoc, hQ.isoPullback_inv_snd, hP.isoPullback_hom_snd]
      exact hc₂
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ComparisonIsomorphism
