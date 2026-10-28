import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientOf

/-! # Quotient Pair Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientPairRelation

noncomputable section

/-! Componentwise compatibility identifies the relation of fiber pairs
with the actual kernel pair of their quotient. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem family_quotient_pair_coequalizes {B X P W V : Scheme.{0}}
    (Y : Over B) (q : X ⟶ Y.left) (q₂ : P ⟶ (Y ⊗ Y).left)
    (p₁ p₂ : P ⟶ X)
    (hp₁ : q₂ ≫ (fst Y Y).left = p₁ ≫ q) (hp₂ : q₂ ≫ (snd Y Y).left = p₂ ≫ q)
    (s t : W ⟶ X) (hq : s ≫ q = t ≫ q) (sp tp : V ⟶ P) (r₁ r₂ : V ⟶ W)
    (hs₁ : r₁ ≫ s = sp ≫ p₁) (hs₂ : r₂ ≫ s = sp ≫ p₂)
    (ht₁ : tp ≫ p₁ = r₁ ≫ t) (ht₂ : tp ≫ p₂ = r₂ ≫ t) :
    sp ≫ q₂ = tp ≫ q₂ := by
  change q₂ ≫ pullback.fst Y.hom Y.hom = p₁ ≫ q at hp₁
  change q₂ ≫ pullback.snd Y.hom Y.hom = p₂ ≫ q at hp₂
  apply pullback.hom_ext
  · rw [Category.assoc, hp₁, ← Category.assoc, ← hs₁, Category.assoc, hq,
      ← Category.assoc, ← ht₁, Category.assoc, Category.assoc, hp₁]
  · rw [Category.assoc, hp₂, ← Category.assoc, ← hs₂, Category.assoc, hq,
      ← Category.assoc, ← ht₂, Category.assoc, Category.assoc, hp₂]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientPairRelation
