import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Picard

/-! # Base Twists -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensoring by a bundle from the test base does not change a relative Picard class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

theorem Picard.BaseTwists.relativePicard_tensor_baseBundle (P T : Over S)
    (L : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor P).obj T)) (B : Line.Bundles.LineBundle T.left) :
    (Picard.PicardSheaf.toRelativePicard P).app (.op T)
        (Line.Bundles.LineBundle.classOf (L.tensor (B.pullback (Limits.pullback.fst T.hom P.hom)))) =
      (Picard.PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf L) := by
  exact (Picard.SheafMonoid.toRelativePicard_mul P T (Line.Bundles.LineBundle.classOf L)
    (Line.Bundles.LineBundle.classOf (B.pullback (Limits.pullback.fst T.hom P.hom)))).trans
      ((congrArg (fun z => (Picard.PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf L) * z)
        ((Picard.BaseBundleTriviality.baseBundle_relativePicardClass_trivial P T B).trans (Picard.SheafMonoid.trivialPicardClass_eq_one P T))).trans
        (mul_one _))

theorem Abelian.Schemes.AbelianScheme.IsHomogeneousPicardClass.translation_class {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (T : Over S) (L : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T))
    (hL : A.IsHomogeneousPicardClass T (Line.Bundles.LineBundle.classOf L)) (a : T ⟶ A.scheme) :
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf (L.pullback (A.translation a).left)) =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf L) := by
  have h := hL T (𝟙 T) a
  have he : (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (𝟙 T).op (Line.Bundles.LineBundle.classOf L) =
      Line.Bundles.LineBundle.classOf L := (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_id_apply (.op T) _
  exact (congrArg (fun q : Line.Bundles.LineBundle.IsoClass ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T) =>
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.pullbackClass (A.translation a).left q)) he).symm.trans
      (h.trans (congrArg (fun q : Line.Bundles.LineBundle.IsoClass ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T) =>
        (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) q) he))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
