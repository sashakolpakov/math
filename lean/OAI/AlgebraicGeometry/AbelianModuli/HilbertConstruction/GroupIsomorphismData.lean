import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Isomorphism Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupIsomorphismData

noncomputable section

/-! A group-object isomorphism is exactly an underlying invertible morphism preserving identity and multiplication. -/

open _root_.CategoryTheory

universe u v

def isoTransportEquiv {C : Type u} [Category.{v} C] {A B X Y : C} (e : A ≅ B) (d : X ≅ Y) :
    (B ≅ Y) ≃ (A ≅ X) where
  toFun h := e ≪≫ h ≪≫ d.symm
  invFun h := e.symm ≪≫ h ≪≫ d
  left_inv h := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  right_inv h := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id]

def groupIsoMorphismEquiv {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (A B : C) [GrpObj A] [GrpObj B] :
    (Grp.mk A ≅ Grp.mk B) ≃ {f : {f : A ⟶ B // IsMonHom f} // IsIso f.val} where
  toFun e := ⟨⟨e.hom.hom.hom, inferInstance⟩, inferInstance⟩
  invFun f := by
    let : IsMonHom f.val.val := f.val.property
    let : IsIso f.val.val := f.property
    exact Grp.mkIso' (asIso f.val.val)
  left_inv e := by
    apply Iso.ext
    apply Grp.hom_ext
    rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupIsomorphismData
