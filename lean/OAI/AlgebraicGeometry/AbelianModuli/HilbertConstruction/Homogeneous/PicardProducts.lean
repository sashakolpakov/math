import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.SheafMonoid
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Picard

/-! # Picard Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Translation-invariant relative Picard classes are closed under tensor multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {g : ℕ} {S : Scheme.{u}}

theorem Homogeneous.PicardProducts.relativePicardPresheaf_map_mul (X : Over S) {T U : Over S} (f : U ⟶ T)
    (q r : (Picard.PicardSheaf.relativePicardPresheaf X).obj (.op T)) :
    (Picard.PicardSheaf.relativePicardPresheaf X).map f.op (q * r) =
      (Picard.PicardSheaf.relativePicardPresheaf X).map f.op q * (Picard.PicardSheaf.relativePicardPresheaf X).map f.op r :=
  Line.Bundles.LineBundle.pullbackClass_mul ((Picard.PicardSheaf.familySchemeFunctor X).map f) q r

theorem Abelian.Schemes.AbelianScheme.IsHomogeneousPicardClass.mul (A : Abelian.Schemes.AbelianScheme g S) {T : Over S}
    {q r : (Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op T)}
    (hq : A.IsHomogeneousPicardClass T q) (hr : A.IsHomogeneousPicardClass T r) :
    A.IsHomogeneousPicardClass T (q * r) := by
  intro U f a
  let τ : (Picard.PicardSheaf.familySchemeFunctor A.scheme).obj U ⟶ (Picard.PicardSheaf.familySchemeFunctor A.scheme).obj U :=
    (A.translation a).left
  let q' : Line.Bundles.LineBundle.IsoClass ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj U) :=
    (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q
  let r' : Line.Bundles.LineBundle.IsoClass ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj U) :=
    (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op r
  have hmap := Homogeneous.PicardProducts.relativePicardPresheaf_map_mul A.scheme f q r
  have hτ := Line.Bundles.LineBundle.pullbackClass_mul τ q' r'
  exact (congrArg (fun z => (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) (Line.Bundles.LineBundle.pullbackClass τ z)) hmap).trans
    ((congrArg (fun z => (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) z) hτ).trans
      ((Picard.SheafMonoid.toRelativePicard_mul A.scheme U (Line.Bundles.LineBundle.pullbackClass τ q') (Line.Bundles.LineBundle.pullbackClass τ r')).trans
        ((congrArg₂ (fun b c : Picard.PicardSheaf.PicardSections A.scheme U => b * c) (hq U f a) (hr U f a)).trans
          ((Picard.SheafMonoid.toRelativePicard_mul A.scheme U q' r').symm.trans
            (congrArg (fun z => (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) z) hmap.symm)))))

def Abelian.Schemes.AbelianScheme.homogeneousPicardSubmonoid (A : Abelian.Schemes.AbelianScheme g S) (T : Over S) :
    Submonoid ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op T)) where
  carrier := A.IsHomogeneousPicardClass T
  one_mem' := A.trivialClass_homogeneous T
  mul_mem' hq hr := hq.mul A hr

instance Abelian.Schemes.AbelianScheme.homogeneousPicardPresheafObjCommMonoid (A : Abelian.Schemes.AbelianScheme g S) (T : (Over S)ᵒᵖ) :
    CommMonoid (A.homogeneousPicardPresheaf.obj T) :=
  inferInstanceAs (CommMonoid (A.homogeneousPicardSubmonoid T.unop))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
