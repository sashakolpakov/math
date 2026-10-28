import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Basic

/-! # Iso Conjugate Square -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsoConjugateSquare.Construction

/-! Canonical comparisons preserve commuting isomorphism squares. -/

open _root_.CategoryTheory

theorem iso_conjugate_square {C : Type*} [Category* C]
    {U V X Y U' V' X' Y' : C}
    (a : U ≅ X) (b : V ≅ Y) (e : U ≅ V)
    (a' : U' ≅ X') (b' : V' ≅ Y') (e' : U' ≅ V')
    (u : U ≅ U') (v : V ≅ V') (x : X ≅ X') (y : Y ≅ Y')
    (ha : a ≪≫ x = u ≪≫ a') (hb : b ≪≫ y = v ≪≫ b') (he : e ≪≫ v = u ≪≫ e') :
    (a.symm ≪≫ e ≪≫ b) ≪≫ y = x ≪≫ (a'.symm ≪≫ e' ≪≫ b') := by
  have hia : a.symm ≪≫ u = x ≪≫ a'.symm := by
    have h := congrArg (fun t => a.symm ≪≫ t ≪≫ a'.symm) ha
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl] using h.symm
  simp only [Iso.trans_assoc]
  rw [hb, ← Iso.trans_assoc e v b', he]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc a.symm u, hia]
  simp only [Iso.trans_assoc]

theorem iso_map_conjugate_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {U V X Y : C} {U' V' X' Y' : D}
    (a : U ≅ X) (b : V ≅ Y) (e : U ≅ V)
    (a' : U' ≅ X') (b' : V' ≅ Y') (e' : U' ≅ V')
    (u : F.obj U ≅ U') (v : F.obj V ≅ V') (x : F.obj X ≅ X') (y : F.obj Y ≅ Y')
    (ha : F.mapIso a ≪≫ x = u ≪≫ a') (hb : F.mapIso b ≪≫ y = v ≪≫ b')
    (he : F.mapIso e ≪≫ v = u ≪≫ e') :
    F.mapIso (a.symm ≪≫ e ≪≫ b) ≪≫ y = x ≪≫ (a'.symm ≪≫ e' ≪≫ b') := by
  rw [Functor.mapIso_trans, Functor.mapIso_trans, Functor.mapIso_symm]
  exact iso_conjugate_square (F.mapIso a) (F.mapIso b) (F.mapIso e) a' b' e' u v x y ha hb he

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsoConjugateSquare.Construction
