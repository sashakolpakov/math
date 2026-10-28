import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientOf

/-! # Quotient Product -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientProduct

noncomputable section

section

/-! The relative product of two cartesian family quotients is cartesian,
with its actual component maps. This applies to the dual and abelian family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem family_quotient_product_cartesian {B T X Z P : Scheme.{0}}
    (u : T ⟶ B) (a : X ⟶ T) (c : Z ⟶ T) (Y D : Over B)
    (q : X ⟶ Y.left) (r : Z ⟶ D.left)
    (hcart : IsPullback a q u Y.hom) (hrcart : IsPullback c r u D.hom)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Z) (hp : IsPullback p₁ p₂ a c) :
    ∃ q₂ : P ⟶ (Y ⊗ D).left,
      q₂ ≫ (fst Y D).left = p₁ ≫ q ∧ q₂ ≫ (snd Y D).left = p₂ ≫ r ∧
      IsPullback (p₁ ≫ a) q₂ u (Y ⊗ D).hom := by
  let q₂ : P ⟶ (Y ⊗ D).left := pullback.lift (p₁ ≫ q) (p₂ ≫ r) (by
    rw [Category.assoc, Category.assoc, ← hcart.w, ← hrcart.w,
      ← Category.assoc, ← Category.assoc, hp.w])
  have h₁ : q₂ ≫ pullback.fst Y.hom D.hom = p₁ ≫ q := pullback.lift_fst _ _ _
  have h₂ : q₂ ≫ pullback.snd Y.hom D.hom = p₂ ≫ r := pullback.lift_snd _ _ _
  refine ⟨q₂, h₁, h₂, ?_⟩
  have hw : (p₁ ≫ a) ≫ u = q₂ ≫ (Y ⊗ D).hom := by
    change _ = q₂ ≫ (pullback.fst Y.hom D.hom ≫ Y.hom)
    rw [← Category.assoc, h₁, Category.assoc, Category.assoc, hcart.w]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw ?_ ?_ ?_ ?_)
  · intro d
    exact hp.lift
      (hcart.lift d.fst (d.snd ≫ pullback.fst Y.hom D.hom) (by
        simpa only [Category.assoc, Over.tensorObj_hom, Over.fst_left] using d.condition))
      (hrcart.lift d.fst (d.snd ≫ pullback.snd Y.hom D.hom) (by
        rw [Category.assoc, ← pullback.condition]
        exact d.condition))
      (by rw [hcart.lift_fst, hrcart.lift_fst])
  · intro d
    rw [← Category.assoc, hp.lift_fst, hcart.lift_fst]
  · intro d
    apply pullback.hom_ext
    · rw [Category.assoc, h₁, ← Category.assoc, hp.lift_fst, hcart.lift_snd]
    · rw [Category.assoc, h₂, ← Category.assoc, hp.lift_snd, hrcart.lift_snd]
  · intro d m hm₁ hm₂
    change m ≫ q₂ = d.snd at hm₂
    apply hp.hom_ext
    · rw [hp.lift_fst]
      apply hcart.hom_ext
      · rw [Category.assoc, hcart.lift_fst]
        exact hm₁
      · rw [Category.assoc, hcart.lift_snd]
        simpa only [Category.assoc, h₁] using congrArg (fun k => k ≫ pullback.fst Y.hom D.hom) hm₂
    · rw [hp.lift_snd]
      apply hrcart.hom_ext
      · rw [Category.assoc, hrcart.lift_fst, ← hp.w]
        exact hm₁
      · rw [Category.assoc, hrcart.lift_snd]
        simpa only [Category.assoc, h₂] using congrArg (fun k => k ≫ pullback.snd Y.hom D.hom) hm₂

end

/-! Compatible relations on two families are coequalized by the actual
relative product quotient. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem family_quotient_product_coequalizes {B X Z P W₁ W₂ V : Scheme.{0}}
    (Y D : Over B) (q : X ⟶ Y.left) (r : Z ⟶ D.left) (q₂ : P ⟶ (Y ⊗ D).left)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Z)
    (hp₁ : q₂ ≫ (fst Y D).left = p₁ ≫ q) (hp₂ : q₂ ≫ (snd Y D).left = p₂ ≫ r)
    (s₁ t₁ : W₁ ⟶ X) (s₂ t₂ : W₂ ⟶ Z)
    (hq : s₁ ≫ q = t₁ ≫ q) (hr : s₂ ≫ r = t₂ ≫ r)
    (sp tp : V ⟶ P) (r₁ : V ⟶ W₁) (r₂ : V ⟶ W₂)
    (hs₁ : r₁ ≫ s₁ = sp ≫ p₁) (hs₂ : r₂ ≫ s₂ = sp ≫ p₂)
    (ht₁ : tp ≫ p₁ = r₁ ≫ t₁) (ht₂ : tp ≫ p₂ = r₂ ≫ t₂) :
    sp ≫ q₂ = tp ≫ q₂ := by
  change q₂ ≫ pullback.fst Y.hom D.hom = p₁ ≫ q at hp₁
  change q₂ ≫ pullback.snd Y.hom D.hom = p₂ ≫ r at hp₂
  apply pullback.hom_ext
  · rw [Category.assoc, hp₁, ← Category.assoc, ← hs₁, Category.assoc, hq,
      ← Category.assoc, ← ht₁, Category.assoc, Category.assoc, hp₁]
  · rw [Category.assoc, hp₂, ← Category.assoc, ← hs₂, Category.assoc, hr,
      ← Category.assoc, ← ht₂, Category.assoc, Category.assoc, hp₂]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientProduct
