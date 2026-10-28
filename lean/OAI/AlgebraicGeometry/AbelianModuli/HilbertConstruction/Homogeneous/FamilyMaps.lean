import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationFamilyMaps

/-! # Family Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Homogeneous Picard classes and sheaves are contravariant under homomorphisms of abelian schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}

/-- Homogeneity of a line-bundle class is preserved by a group-scheme pullback. -/
theorem Abelian.Schemes.AbelianScheme.IsHomogeneousPicardClass.familyMap
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] {T : Over S}
    {q : (Picard.PicardSheaf.relativePicardPresheaf B.scheme).obj (.op T)} (hq : B.IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass T ((Picard.FamilyMaps.relativePicardPresheafMap f).app (.op T) q) := by
  intro U k a
  have ht := Abelian.Schemes.AbelianScheme.TranslationInvariant.familyMap f a
    ((Picard.PicardSheaf.relativePicardPresheaf B.scheme).map k.op q) (hq U k (a ≫ f))
  have hn := (Picard.FamilyMaps.relativePicardPresheafMap f).naturality_apply k.op q
  exact (congrArg (fun q' => A.TranslationInvariant a q') hn).mp ht

/-- Pullback on the presheaf of homogeneous bundle classes. -/
def Homogeneous.FamilyMaps.homogeneousPicardPresheafMap (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    B.homogeneousPicardPresheaf ⟶ A.homogeneousPicardPresheaf where
  app T := TypeCat.ofHom (fun q => ⟨(Picard.FamilyMaps.relativePicardPresheafMap f).app T q.val, q.property.familyMap f⟩)
  naturality T U k := by
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (Picard.FamilyMaps.relativePicardPresheafMap f).naturality_apply k q.val

/-- An abelian-scheme isomorphism identifies the homogeneous Picard presheaves. -/
def Homogeneous.FamilyMaps.homogeneousPicardPresheafFamilyIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    B.homogeneousPicardPresheaf ≅ A.homogeneousPicardPresheaf where
  hom := Homogeneous.FamilyMaps.homogeneousPicardPresheafMap e.hom
  inv := Homogeneous.FamilyMaps.homogeneousPicardPresheafMap e.inv
  hom_inv_id := by
    apply NatTrans.ext
    funext T
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (Picard.FamilyMaps.relativePicardPresheafIso e).hom_inv_id T) q.val
  inv_hom_id := by
    apply NatTrans.ext
    funext T
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (Picard.FamilyMaps.relativePicardPresheafIso e).inv_hom_id T) q.val

/-- The homogeneous Picard sheaf is invariant under abelian-scheme isomorphism. -/
def Homogeneous.FamilyMaps.homogeneousPicardFamilyIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    B.homogeneousPicardSheaf ≅ A.homogeneousPicardSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso
    (Homogeneous.FamilyMaps.homogeneousPicardPresheafFamilyIso e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
