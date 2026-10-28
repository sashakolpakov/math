import Mathlib.CategoryTheory.NatIso

/-! # Gluing Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingTransport

noncomputable section

/-!
# Transport of gluing across a natural comparison
-/

open _root_.CategoryTheory

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]

/-- Naturality expressed as conjugation by a natural isomorphism. -/
theorem naturality_conjugate {Q H : C ⥤ D} (η : Q ≅ H) {X Y : C} (a : X ⟶ Y) :
    H.map a = η.inv.app X ≫ Q.map a ≫ η.hom.app Y := by
  apply (cancel_mono (η.inv.app Y)).mp
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  exact η.inv.naturality a

/-- A natural comparison carries a map between presented objects to the conjugated geometric map. -/
theorem transfer (Q : C ⥤ D) (H : C ⥤ E) (G : D ⥤ F) (J : E ⥤ F)
    (η : Q ⋙ G ≅ H ⋙ J) {X Y : C} {U V : E} {A B : D}
    (c₁ : U ≅ H.obj X) (c₂ : V ≅ H.obj Y)
    (e₁ : Q.obj X ≅ A) (e₂ : Q.obj Y ≅ B)
    (a : X ⟶ Y) (b : A ⟶ B) (h : Q.map a = e₁.hom ≫ b ≫ e₂.inv) :
    J.map (c₁.hom ≫ H.map a ≫ c₂.inv) =
      (J.mapIso c₁ ≪≫ (η.app X).symm ≪≫ G.mapIso e₁).hom ≫ G.map b ≫
        (J.mapIso c₂ ≪≫ (η.app Y).symm ≪≫ G.mapIso e₂).inv := by
  rw [J.map_comp, J.map_comp]
  have hn := naturality_conjugate η a
  change J.map (H.map a) = η.inv.app X ≫ G.map (Q.map a) ≫ η.hom.app Y at hn
  rw [hn, h]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    G.map_comp, Category.assoc]

/-- Compatibility with composition determines the total comparison isomorphism. -/
theorem comparison (J : C ⥤ D) (G : E ⥤ D) {U V : C} {A B : E} {W : D}
    (c : U ≅ V) (η : G.obj A ≅ J.obj V) (e : A ≅ B)
    (d : J.obj U ≅ W) (b : G.obj B ≅ W)
    (h : J.map c.inv ≫ d.hom = η.inv ≫ G.map e.hom ≫ b.hom) :
    J.mapIso c ≪≫ η.symm ≪≫ G.mapIso e = d ≪≫ b.symm := by
  apply Iso.ext
  apply (cancel_mono b.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc, ← J.map_comp, c.hom_inv_id, J.map_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingTransport
