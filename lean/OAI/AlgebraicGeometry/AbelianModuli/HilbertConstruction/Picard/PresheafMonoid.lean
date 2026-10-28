import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassMonoid
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.CommMon_

/-! # Presheaf Monoid -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PresheafMonoid

noncomputable section

/-! The presheaf of line-bundle classes has its actual tensor-product commutative monoid structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}}

def lineBundleClassCommMonFunctor : Scheme.{u}ᵒᵖ ⥤ CommMonCat.{u + 1} where
  obj X := CommMonCat.of (Line.Bundles.LineBundle.IsoClass X.unop)
  map f := CommMonCat.ofHom (Line.Bundles.LineBundle.pullbackClassMonoidHom f.unop)
  map_id X := by
    apply CommMonCat.hom_ext
    exact Line.Bundles.LineBundle.pullbackClassMonoidHom_id
  map_comp f g := by
    apply CommMonCat.hom_ext
    exact Line.Bundles.LineBundle.pullbackClassMonoidHom_comp g.unop f.unop

instance relativePicardPresheafObjCommMonoid (X : Over S) (T : (Over S)ᵒᵖ) :
    CommMonoid ((PicardSheaf.relativePicardPresheaf X).obj T) :=
  Line.Bundles.LineBundle.isoClassCommMonoid ((PicardSheaf.familySchemeFunctor X).obj T.unop)

instance relativePicardPresheafMonObj (X : Over S) : MonObj (PicardSheaf.relativePicardPresheaf X) where
  one :=
    { app T := TypeCat.ofHom (fun _ => (1 : Line.Bundles.LineBundle.IsoClass ((PicardSheaf.familySchemeFunctor X).obj T.unop)))
      naturality {T U} f := by
        apply ConcreteCategory.ext_apply
        intro q
        exact (Line.Bundles.LineBundle.pullbackClass_trivial ((PicardSheaf.familySchemeFunctor X).map f.unop)).symm }
  mul :=
    { app T := TypeCat.ofHom (fun p => p.1 * p.2)
      naturality {T U} f := by
        apply ConcreteCategory.ext_apply
        intro q
        exact (Line.Bundles.LineBundle.pullbackClass_mul ((PicardSheaf.familySchemeFunctor X).map f.unop) q.1 q.2).symm }
  one_mul := by
    ext T q
    exact one_mul q.2
  mul_one := by
    ext T q
    exact mul_one q.1
  mul_assoc := by
    ext T q
    exact mul_assoc q.1.1 q.1.2 q.2

instance relativePicardPresheafIsCommMonObj (X : Over S) : IsCommMonObj (PicardSheaf.relativePicardPresheaf X) where
  mul_comm := by
    ext T q
    exact mul_comm q.2 q.1

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PresheafMonoid
