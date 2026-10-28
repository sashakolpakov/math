import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

/-! # Family Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.FamilyMaps

noncomputable section

/-! The relative Picard presheaf is contravariant in the family scheme as well as in the test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} {X Y Z : Over S}

/-- A map of families induces maps of their total spaces over every test scheme. -/
def familySchemeMap (f : X ⟶ Y) : PicardSheaf.familySchemeFunctor X ⟶ PicardSheaf.familySchemeFunctor Y where
  app T := (𝟙 T ⊗ₘ f).left
  naturality T U h := by
    change (h ⊗ₘ 𝟙 X).left ≫ (𝟙 U ⊗ₘ f).left = (𝟙 T ⊗ₘ f).left ≫ (h ⊗ₘ 𝟙 Y).left
    have he : (h ⊗ₘ 𝟙 X) ≫ (𝟙 U ⊗ₘ f) = (𝟙 T ⊗ₘ f) ≫ (h ⊗ₘ 𝟙 Y) := by
      simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    exact congrArg Over.Hom.left he

/-- Pull back line-bundle classes along a morphism of the represented families. -/
def relativePicardPresheafMap (f : X ⟶ Y) : PicardSheaf.relativePicardPresheaf Y ⟶ PicardSheaf.relativePicardPresheaf X :=
  Functor.whiskerRight (NatTrans.op (familySchemeMap f)) Line.Bundles.lineBundleClassFunctor

theorem relativePicardPresheafMap_apply (f : X ⟶ Y) (T : Over S)
    (q : (PicardSheaf.relativePicardPresheaf Y).obj (.op T)) :
    (relativePicardPresheafMap f).app (.op T) q = Line.Bundles.LineBundle.pullbackClass (𝟙 T ⊗ₘ f).left q := rfl

theorem relativePicardPresheafMap_id (X : Over S) : relativePicardPresheafMap (𝟙 X) = 𝟙 _ := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  change Line.Bundles.LineBundle.pullbackClass (𝟙 T.unop ⊗ₘ 𝟙 X).left q = q
  have he : (𝟙 T.unop ⊗ₘ 𝟙 X).left = 𝟙 (T.unop ⊗ X).left :=
    congrArg Over.Hom.left (id_tensorHom_id _ _)
  exact (congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f q) he).trans (Line.Bundles.LineBundle.pullbackClass_id q)

theorem relativePicardPresheafMap_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativePicardPresheafMap (f ≫ h) = relativePicardPresheafMap h ≫ relativePicardPresheafMap f := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  change Line.Bundles.LineBundle.pullbackClass (𝟙 T.unop ⊗ₘ (f ≫ h)).left q =
    Line.Bundles.LineBundle.pullbackClass (𝟙 T.unop ⊗ₘ f).left (Line.Bundles.LineBundle.pullbackClass (𝟙 T.unop ⊗ₘ h).left q)
  have he : (𝟙 T.unop ⊗ₘ (f ≫ h)).left =
      (𝟙 T.unop ⊗ₘ f).left ≫ (𝟙 T.unop ⊗ₘ h).left := by
    have hc : (𝟙 T.unop ⊗ₘ f) ≫ (𝟙 T.unop ⊗ₘ h) = 𝟙 T.unop ⊗ₘ (f ≫ h) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp]
    exact (congrArg Over.Hom.left hc).symm
  exact (congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f q) he).trans (Line.Bundles.LineBundle.pullbackClass_comp _ _ q)

/-- An isomorphism of family schemes induces an isomorphism of relative Picard presheaves. -/
def relativePicardPresheafIso (e : X ≅ Y) : PicardSheaf.relativePicardPresheaf Y ≅ PicardSheaf.relativePicardPresheaf X where
  hom := relativePicardPresheafMap e.hom
  inv := relativePicardPresheafMap e.inv
  hom_inv_id := (relativePicardPresheafMap_comp e.inv e.hom).symm.trans
    ((congrArg relativePicardPresheafMap e.inv_hom_id).trans (relativePicardPresheafMap_id Y))
  inv_hom_id := (relativePicardPresheafMap_comp e.hom e.inv).symm.trans
    ((congrArg relativePicardPresheafMap e.hom_inv_id).trans (relativePicardPresheafMap_id X))

/-- The relative Picard sheaf is invariant under isomorphism of its family scheme. -/
def relativePicardFamilyIso (e : X ≅ Y) : PicardSheaf.relativePicardSheaf Y ≅ PicardSheaf.relativePicardSheaf X :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso (relativePicardPresheafIso e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.FamilyMaps
