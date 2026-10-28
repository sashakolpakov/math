import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseTwists
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationSectionFibers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.RelativePicardInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.Support

/-! # Translation Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The translation formula for normalized homogeneous line bundles over arbitrary test schemes over a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))

theorem Abelian.Schemes.AbelianScheme.homogeneous_translation_iso
    (T : Over (Spec (.of K))) (L : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T))
    (hL : A.IsHomogeneousPicardClass T (Line.Bundles.LineBundle.classOf L))
    (e₀ : (L.pullback (A.familyZeroSection T)).sheaf ≅ Line.Bundles.structureModule T.left)
    (a : T ⟶ A.scheme) :
    Nonempty ((L.pullback (A.translation a).left).sheaf ≅
      (L.tensor ((L.pullback (A.familyPointSection T a)).pullback
        (Limits.pullback.fst T.hom A.scheme.hom))).sheaf) := by
  have : IsReduced A.scheme.left := A.reduced_overField
  have : ConnectedSpace A.scheme.left := A.connected_overField
  let B := L.pullback (A.familyPointSection T a)
  exact Proper.RelativePicardInjectivity.properField_bundleIso_of_relativePicard_eq A.scheme η[A.scheme].left η[A.scheme].w T
    (L.pullback (A.translation a).left) (L.tensor (B.pullback (Limits.pullback.fst T.hom A.scheme.hom)))
    (A.familyZeroSection T) (A.familyZeroSection_fst T)
    (TranslationSectionFibers.translatedBundle_zeroIso A T a L ≪≫ (TranslationSectionFibers.normalizedBaseTwist_zeroIso A T L B e₀).symm)
    ((hL.translation_class A T L a).trans (Picard.BaseTwists.relativePicard_tensor_baseBundle A.scheme T L B).symm)

theorem Dual.Data.DualAbelianData.poincareAt_translation_iso (D : Dual.Data.DualAbelianData A)
    {T : Over (Spec (.of K))} (f : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    Nonempty (((D.poincareAt f).pullback (A.translation a).left).sheaf ≅
      ((D.poincareAt f).tensor (((D.poincareAt f).pullback (A.familyPointSection T a)).pullback
        (Limits.pullback.fst T.hom A.scheme.hom))).sheaf) :=
  A.homogeneous_translation_iso T (D.poincareAt f) (D.poincareHomogeneous.pullback A f)
    (D.poincareAt_zeroIso f) a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
