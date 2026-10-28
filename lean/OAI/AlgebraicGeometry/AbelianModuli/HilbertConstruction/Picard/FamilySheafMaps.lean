import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.FamilyMaps

/-! # Family Sheaf Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps

noncomputable section

/-! Family morphisms act on the relative Picard sheaf compatibly with actual line-bundle classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X Y : Over S}

/-- Pull back the relative Picard sheaf along a morphism of family schemes. -/
def relativePicardSheafMap (f : X ⟶ Y) : PicardSheaf.relativePicardSheaf Y ⟶ PicardSheaf.relativePicardSheaf X :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map (FamilyMaps.relativePicardPresheafMap f)

/-- Pullback of actual bundle classes agrees with the induced map on Picard sheaves. -/
theorem relativePicardSheafMap_toRelative (f : X ⟶ Y) (T : Over S)
    (q : (PicardSheaf.relativePicardPresheaf Y).obj (.op T)) :
    (relativePicardSheafMap f).hom.app (.op T) ((PicardSheaf.toRelativePicard Y).app (.op T) q) =
      (PicardSheaf.toRelativePicard X).app (.op T) ((FamilyMaps.relativePicardPresheafMap f).app (.op T) q) :=
  (ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (Scheme.fppfTopology.over S)
      (FamilyMaps.relativePicardPresheafMap f)) (.op T)) q).symm

/-- The induced family map preserves the trivial Picard class. -/
theorem relativePicardSheafMap_trivial (f : X ⟶ Y) (T : Over S) :
    (relativePicardSheafMap f).hom.app (.op T) (PicardSheaf.trivialPicardClass Y T) = PicardSheaf.trivialPicardClass X T :=
  (relativePicardSheafMap_toRelative f T
    (Line.Bundles.LineBundle.trivialClass ((PicardSheaf.familySchemeFunctor Y).obj T))).trans
      (congrArg (fun q => (PicardSheaf.toRelativePicard X).app (.op T) q)
        (Line.Bundles.LineBundle.pullbackClass_trivial ((FamilyMaps.familySchemeMap f).app T)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps
