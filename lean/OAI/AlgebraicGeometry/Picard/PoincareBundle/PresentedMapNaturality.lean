import Mathlib.CategoryTheory.NatIso

/-! # Presented Map Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedMapNaturality

noncomputable section

/-!
# Naturality of a map after choosing presentations of its source and target
-/

open _root_.CategoryTheory

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]

/-- Present a morphism by given geometric identifications of its two objects. -/
def presentedMap (H : C ⥤ D) {M N : C} {X Y : D}
    (eM : H.obj M ≅ X) (eN : H.obj N ≅ Y) (a : M ⟶ N) : X ⟶ Y :=
  eM.inv ≫ H.map a ≫ eN.hom

/-- An isomorphism between modules gives an isomorphism between their presented objects. -/
def presentedIso (H : C ⥤ D) {M N : C} {X Y : D}
    (eM : H.obj M ≅ X) (eN : H.obj N ≅ Y) (a : M ≅ N) : X ≅ Y :=
  eM.symm ≪≫ H.mapIso a ≪≫ eN

theorem presentedIso_hom (H : C ⥤ D) {M N : C} {X Y : D}
    (eM : H.obj M ≅ X) (eN : H.obj N ≅ Y) (a : M ≅ N) :
    (presentedIso H eM eN a).hom = presentedMap H eM eN a.hom := rfl

/-- A natural comparison commutes with these presented morphisms. -/
theorem naturality (P : C ⥤ E) (H : C ⥤ D) (K : E ⥤ F) (Q : D ⥤ F)
    (η : P ⋙ K ≅ H ⋙ Q) {M N : C} {X Y : D}
    (eM : H.obj M ≅ X) (eN : H.obj N ≅ Y) (a : M ⟶ N) :
    K.map (P.map a) ≫ ((η.app N) ≪≫ Q.mapIso eN).hom =
      ((η.app M) ≪≫ Q.mapIso eM).hom ≫ Q.map (presentedMap H eM eN a) := by
  have hn := η.hom.naturality a
  change K.map (P.map a) ≫ η.hom.app N = η.hom.app M ≫ Q.map (H.map a) at hn
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, presentedMap,
    Q.map_comp, Category.assoc]
  have he : Q.map eM.hom ≫ Q.map eM.inv = 𝟙 _ := by
    rw [← Q.map_comp, eM.hom_inv_id, Q.map_id]
  rw [← Category.assoc (Q.map eM.hom) (Q.map eM.inv), he, Category.id_comp]
  rw [← Category.assoc (K.map (P.map a)) (η.hom.app N), hn]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedMapNaturality
