import OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousGroup

/-! # Group Functor -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupFunctor

noncomputable section

/-! A group-valued functor on the existing type-valued Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}}

def picardTypeGroupSheafFunctor (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1}) :
    (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of ((sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T)
  map f := CommGrpCat.ofHom (GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom P f)
  map_id T := by
    ext q
    change GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom P (𝟙 T) q = q
    rw [GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply]
    exact (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).map_id_apply T q
  map_comp f g := by
    ext q
    change GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom P (f ≫ g) q =
      GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom P g (GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom P f q)
    rw [GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply, GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply,
      GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply]
    exact (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).map_comp_apply f g q

def picardTypeGroupForgetIso (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1}) :
    picardTypeGroupSheafFunctor P ⋙ forget CommGrpCat ≅
      sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro T U f
    ext q
    exact GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply P f q)

def homogeneousPicardGroupFunctor {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} :=
  picardTypeGroupSheafFunctor (HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf A)

def homogeneousPicardGroupForgetIso {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    homogeneousPicardGroupFunctor A ⋙ forget CommGrpCat ≅ A.homogeneousPicardSheaf.obj :=
  picardTypeGroupForgetIso (HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf A)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupFunctor
