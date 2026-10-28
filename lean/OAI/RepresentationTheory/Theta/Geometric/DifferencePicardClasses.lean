import OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass
import OAI.RepresentationTheory.Theta.Geometric.DescendedDifferenceAxis

/-! # Difference Picard Classes -/

namespace OAI.RepresentationTheory.Theta.Geometric.DifferencePicardClasses

noncomputable section

/-! The natural Picard family of the descended bundle pulls back to
the original theta difference family, with its exact line-class formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem parameterLineClass_congr {S : Scheme} {A P : Over S}
    (Q R : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left) (e : Q.sheaf ≅ R.sheaf)
    {T : Over S} (t : T ⟶ P) : ParameterizedPicardClass.parameterLineClass Q t = ParameterizedPicardClass.parameterLineClass R t :=
  Quotient.sound ⟨(Scheme.Modules.pullback (t ⊗ₘ 𝟙 A).left).mapIso e⟩

theorem parameterDifference_product_mul {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (t : T ⟶ A.scheme) :
    (t ⊗ₘ 𝟙 A.scheme) ≫ μ[A.scheme] = A.translation t ≫ snd T A.scheme := by
  have hmul : μ[A.scheme] = fst A.scheme A.scheme * snd A.scheme A.scheme := by
    change μ[A.scheme] = lift (fst A.scheme A.scheme) (snd A.scheme A.scheme) ≫ μ[A.scheme]
    simp
  rw [hmul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, Category.comp_id,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_snd]

theorem parameterDifference_class {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (t : T ⟶ A.scheme) :
    ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) t =
      Picard.PicardPullback.picardPullback (A.translation t).left
        (Picard.PicardPullback.picardPullback (snd T A.scheme).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) *
      (Picard.PicardPullback.picardPullback (fst T A.scheme).left
        (Picard.PicardPullback.picardPullback t.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)))⁻¹ *
      (Picard.PicardPullback.picardPullback (snd T A.scheme).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))⁻¹ := by
  have H := Picard.PicardPullback.algebraicDifferenceBundle_pullback_class L (fst A.scheme A.scheme).left
    (snd A.scheme A.scheme).left μ[A.scheme].left (t ⊗ₘ 𝟙 A.scheme).left
  rw [show (t ⊗ₘ 𝟙 A.scheme).left ≫ μ[A.scheme].left =
    (A.translation t).left ≫ (snd T A.scheme).left from
      congrArg Over.Hom.left (parameterDifference_product_mul A t),
    show (t ⊗ₘ 𝟙 A.scheme).left ≫ (fst A.scheme A.scheme).left =
      (fst T A.scheme).left ≫ t.left from congrArg Over.Hom.left (tensorHom_fst t (𝟙 A.scheme)),
    show (t ⊗ₘ 𝟙 A.scheme).left ≫ (snd A.scheme A.scheme).left =
      (snd T A.scheme).left from congrArg Over.Hom.left
        ((tensorHom_snd t (𝟙 A.scheme)).trans (Category.comp_id _))] at H
  rw [Picard.PicardPullback.picardPullback_comp, Picard.PicardPullback.picardPullback_comp]
  exact H

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

theorem descendedDifference_parameterClass {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (t : T ⟶ A.scheme) :
    ParameterizedPicardClass.parameterLineClass (DescendedDifferenceBundle.descendedDifferenceBundle p labels L hL e) (t ≫ p.hom) =
      ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) t :=
  (ParameterizedPicardClass.parameterLineClass_baseChange _ p.hom t).trans
    (parameterLineClass_congr _ _ (DescendedDifferenceBundle.descendedDifferenceBundle_pullbackIso p labels L hL e) t)

theorem descendedDifference_parameterClass_normalized {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (t : T ⟶ B.scheme) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A.scheme)).left
      (ParameterizedPicardClass.parameterLineClass (DescendedDifferenceBundle.descendedDifferenceBundle p labels L hL e) t) = 1 :=
  ParameterizedPicardClass.parameterLineClass_normalized _ (DescendedDifferenceAxis.descendedDifferenceBundle_zeroIso p labels L hL e) t

theorem descendedDifference_parameterPicardClass_one (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    ParameterizedPicardClass.parameterPicardClass (DescendedDifferenceBundle.descendedDifferenceBundle p labels L hL e) (1 : T ⟶ B.scheme) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme T :=
  ParameterizedPicardClass.parameterPicardClass_one _ (DescendedDifferenceBundle.descendedDifferenceBundle_dualZeroIso p labels L hL e) T

end

end OAI.RepresentationTheory.Theta.Geometric.DifferencePicardClasses
