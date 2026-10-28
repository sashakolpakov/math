import Mathlib.CategoryTheory.Iso

/-! # Tangent Sources Based -/

namespace OAI.RepresentationTheory.Theta.Geometric.TangentSourcesBased

noncomputable section

/-! Changing the presentations of a pointed infinitesimal test preserves
its actual scheme-morphism fiber. -/

open _root_.CategoryTheory

def basedHomEquiv {C : Type*} [Category C] {A B A' B' X : C}
    (t : A ⟶ B) (t' : A' ⟶ B') (e₀ : A ≅ A') (e : B ≅ B')
    (ht : e₀.hom ≫ t' = t ≫ e.hom) (p : A ⟶ X) :
    {f : B ⟶ X // t ≫ f = p} ≃ {f : B' ⟶ X // t' ≫ f = e₀.inv ≫ p} where
  toFun f := ⟨e.inv ≫ f.val, by
    apply (cancel_epi e₀.hom).mp
    rw [← Category.assoc, ht, Category.assoc, Iso.hom_inv_id_assoc, f.property,
      Iso.hom_inv_id_assoc]⟩
  invFun f := ⟨e.hom ≫ f.val, by
    rw [← Category.assoc, ← ht, Category.assoc, f.property, Iso.hom_inv_id_assoc]⟩
  left_inv f := Subtype.ext (e.hom_inv_id_assoc f.val)
  right_inv f := Subtype.ext (e.inv_hom_id_assoc f.val)

theorem basedHomEquiv_apply {C : Type*} [Category C] {A B A' B' X : C}
    (t : A ⟶ B) (t' : A' ⟶ B') (e₀ : A ≅ A') (e : B ≅ B')
    (ht : e₀.hom ≫ t' = t ≫ e.hom) (p : A ⟶ X) (f : {f : B ⟶ X // t ≫ f = p}) :
    (basedHomEquiv t t' e₀ e ht p f).val = e.inv ≫ f.val := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.TangentSourcesBased
