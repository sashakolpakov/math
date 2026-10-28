import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupSheafMaps
import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPowerGroup

/-! # Relative Group -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup

noncomputable section

/-! The intrinsic group law on the existing relative fppf Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}}

def relativePicardGroupPresheaf (X : Over S) : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} :=
  (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor X).op ⋙ SchemePullback.Construction.schemePicardFunctor

instance relativePicardClassCommGroup (X : Over S) (T : (Over S)ᵒᵖ) :
    CommGroup ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf X).obj T) :=
  inferInstanceAs (CommGroup (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor X).obj T.unop)))

instance relativePicardSectionsCommGroup (X : Over S) (T : (Over S)ᵒᵖ) :
    CommGroup ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf X).obj.obj T) :=
  GroupSheafification.Construction.picardTypeSheafifyCommGroup (relativePicardGroupPresheaf X) T

def toRelativePicardHom (X T : Over S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor X).obj T) →* AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections X T :=
  GroupSheafification.Construction.picardTypeSheafifyUnitHom (relativePicardGroupPresheaf X) (op T)

theorem toRelativePicard_mul (X T : Over S)
    (a b : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor X).obj T)) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard X).app (op T) (a * b) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard X).app (op T) a * (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard X).app (op T) b :=
  (toRelativePicardHom X T).map_mul a b

theorem toRelativePicard_inv (X T : Over S)
    (a : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor X).obj T)) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard X).app (op T) a⁻¹ = ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard X).app (op T) a)⁻¹ :=
  (toRelativePicardHom X T).map_inv a

theorem toRelativePicard_pow (X T : Over S)
    (a : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor X).obj T)) (n : ℕ) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard X).app (op T) (a ^ n) = ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard X).app (op T) a) ^ n :=
  (toRelativePicardHom X T).map_pow a n

theorem trivialPicardClass_eq_one (X T : Over S) : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass X T = 1 :=
  (toRelativePicardHom X T).map_one

def relativePicardRestrictHom (X : Over S) {T U : Over S} (f : U ⟶ T) :
    AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections X T →* AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections X U :=
  GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom (relativePicardGroupPresheaf X) f.op

theorem relativePicardRestrictHom_apply (X : Over S) {T U : Over S} (f : U ⟶ T)
    (q : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections X T) :
    relativePicardRestrictHom X f q = (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf X).obj.map f.op q :=
  GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply (relativePicardGroupPresheaf X) f.op q

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup
