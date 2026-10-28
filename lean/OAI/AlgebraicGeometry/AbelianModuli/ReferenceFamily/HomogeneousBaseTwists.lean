import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Picard

/-! # Homogeneous Base Twists -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousBaseTwists

noncomputable section

/-! Normalizing a line bundle along the abelian identity preserves
its original, all-test homogeneity condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist

universe u
variable {S : Scheme.{u}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem baseTwist_translation {T : Over S} (a : T ⟶ A.scheme)
    (m : HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) (q : (HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op T)) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left (FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.baseTwist A.scheme m q) =
      FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.baseTwist A.scheme m (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left q) := by
  change HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left at q
  change Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (A.translation a).left
      (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst T A.scheme).left m * q) = _
  rw [map_mul]
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left
      (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst T A.scheme).left m) * _ = _
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have he : (A.translation a).left ≫ (fst T A.scheme).left = (fst T A.scheme).left :=
    congrArg Over.Hom.left (A.translation_fst a)
  rw [he]
  rfl

theorem homogeneous_baseTwist {T : Over S}
    (m : HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) (q : (HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op T))
    (hq : A.IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass T (FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.baseTwist A.scheme m q) := by
  intro U f a
  rw [FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.baseTwist_natural]
  exact (congrArg ((HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U))
    (baseTwist_translation A a (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left m)
      ((HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q))).trans
        ((FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.toRelativePicard_baseTwist_class A.scheme _ _).trans
          ((hq U f a).trans (FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.toRelativePicard_baseTwist_class A.scheme _ _).symm))

theorem normalizedProductClass_homogeneous {T : Over S}
    (q : (HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op T))
    (hq : A.IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass T (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A.scheme T q) := by
  change HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left at q
  have he : FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A.scheme T q = FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.baseTwist A.scheme
      (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A.scheme)).left q)⁻¹ q := by
    change q / Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (fst T A.scheme).left _ =
      Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (fst T A.scheme).left _ * q
    rw [map_inv, div_eq_mul_inv, mul_comm]
    rfl
  exact (congrArg (A.IsHomogeneousPicardClass T) he).mpr (homogeneous_baseTwist A _ q hq)

theorem normalizedProductBundle_homogeneous {T : Over S}
    (L : HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)
    (hL : A.IsHomogeneousPicardClass T (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    A.IsHomogeneousPicardClass T (HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme T L)) := by
  exact (congrArg (A.IsHomogeneousPicardClass T)
    (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class A.scheme T L)).mpr (normalizedProductClass_homogeneous A _ hL)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousBaseTwists
