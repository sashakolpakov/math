import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PresheafMonoid
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafMonoidSections

/-! # Sheaf Monoid -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.SheafMonoid

noncomputable section

/-! The relative Picard sheaf carries tensor multiplication, with the canonical class map preserving products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

instance relativePicardSheafMonObj (X : Over S) : MonObj (PicardSheaf.relativePicardSheaf X).obj :=
  SheafificationMonoids.sheafifyMonObj (Scheme.fppfTopology.over S) (PicardSheaf.relativePicardPresheaf X)

instance relativePicardSheafIsCommMonObj (X : Over S) : IsCommMonObj (PicardSheaf.relativePicardSheaf X).obj :=
  SheafificationMonoids.sheafifyIsCommMonObj (Scheme.fppfTopology.over S) (PicardSheaf.relativePicardPresheaf X)

instance toRelativePicardIsMonHom (X : Over S) : IsMonHom (PicardSheaf.toRelativePicard X) :=
  SheafificationMonoids.toSheafifyIsMonHom (Scheme.fppfTopology.over S) (PicardSheaf.relativePicardPresheaf X)

instance picardSectionsCommMonoid (X T : Over S) : CommMonoid (PicardSheaf.PicardSections X T) :=
  PresheafMonoidSections.presheafSectionsCommMonoid (PicardSheaf.relativePicardSheaf X).obj (.op T)

theorem toRelativePicard_one (X T : Over S) :
    (PicardSheaf.toRelativePicard X).app (.op T) 1 = (1 : PicardSheaf.PicardSections X T) :=
  ConcreteCategory.congr_hom (CC := fun X : Type (u + 1) => X) (congr_app (IsMonHom.one_hom (PicardSheaf.toRelativePicard X)) (.op T)) PUnit.unit

theorem toRelativePicard_mul (X T : Over S) (a b : (PicardSheaf.relativePicardPresheaf X).obj (.op T)) :
    (PicardSheaf.toRelativePicard X).app (.op T) (a * b) =
      (PicardSheaf.toRelativePicard X).app (.op T) a * (PicardSheaf.toRelativePicard X).app (.op T) b :=
  ConcreteCategory.congr_hom (CC := fun X : Type (u + 1) => X) (congr_app (IsMonHom.mul_hom (PicardSheaf.toRelativePicard X)) (.op T)) (a, b)

@[simp]
theorem trivialPicardClass_eq_one (X T : Over S) : PicardSheaf.trivialPicardClass X T = 1 :=
  toRelativePicard_one X T

theorem picardSections_map_mul (X : Over S) {T U : Over S} (f : U ⟶ T) (a b : PicardSheaf.PicardSections X T) :
    (PicardSheaf.relativePicardSheaf X).obj.map f.op (a * b) =
      (PicardSheaf.relativePicardSheaf X).obj.map f.op a * (PicardSheaf.relativePicardSheaf X).obj.map f.op b :=
  PresheafMonoidSections.presheafSections_map_mul (PicardSheaf.relativePicardSheaf X).obj f.op a b

def picardSectionsRestriction (X : Over S) {T U : Over S} (f : U ⟶ T) :
    PicardSheaf.PicardSections X T →* PicardSheaf.PicardSections X U where
  toFun := (PicardSheaf.relativePicardSheaf X).obj.map f.op
  map_one' := PresheafMonoidSections.presheafSections_map_one (PicardSheaf.relativePicardSheaf X).obj f.op
  map_mul' := picardSections_map_mul X f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.SheafMonoid
