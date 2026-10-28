import OAI.RepresentationTheory.Theta.Geometric.DifferenceKernelLinearization
import OAI.RepresentationTheory.Theta.Geometric.QuotientDifferenceNormalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Descended Difference Bundle -/

namespace OAI.RepresentationTheory.Theta.Geometric.DescendedDifferenceBundle

noncomputable section

/-! The coherent difference-bundle kernel transport effectively
descends to the actual quotient product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {g h : ℕ} {A : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

def differenceDescentDatum : OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (p.hom ⊗ₘ 𝟙 A.scheme).left) :=
  OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent.underlyingDatum OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => p.hom ⊗ₘ 𝟙 A.scheme)
    (DifferenceKernelLinearization.differenceKernelLinearization p labels L hL e).toDescentData

theorem differenceDescentDatum_isLine : OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles.IsLine ((differenceDescentDatum p labels L hL e).obj PUnit.unit) :=
  (AbelianDifferenceBundle.abelianDifferenceBundle A L).locallyTrivial

local instance descendedDifferenceProduct_affine : IsAffineHom (p.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : IsAffineHom (Over.Hom.left (𝟙 A.scheme)) := inferInstanceAs (IsAffineHom (𝟙 A.scheme.left))
  exact OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers.tensorAffine p.hom (𝟙 A.scheme)

local instance descendedDifferenceProduct_flat : Flat (p.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : Flat (Over.Hom.left (𝟙 A.scheme)) := inferInstanceAs (Flat (𝟙 A.scheme.left))
  exact OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers.tensorFlat p.hom (𝟙 A.scheme)

local instance descendedDifferenceProduct_surjective : Surjective (p.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : Surjective (Over.Hom.left (𝟙 A.scheme)) := inferInstanceAs (Surjective (𝟙 A.scheme.left))
  exact OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers.tensorSurjective p.hom (𝟙 A.scheme)

local instance descendedDifferenceProduct_noetherian : IsLocallyNoetherian (B.scheme ⊗ A.scheme).left := by
  have : LocallyOfFiniteType (B.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (B.scheme ⊗ A.scheme).hom

def descendedDifferenceBundle : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B.scheme ⊗ A.scheme).left :=
  let D := OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLine (p.hom ⊗ₘ 𝟙 A.scheme).left
    (differenceDescentDatum p labels L hL e) (differenceDescentDatum_isLine p labels L hL e)
  ⟨D.sheaf, D.isLine⟩

def descendedDifferenceBundle_pullbackIso :
    ((descendedDifferenceBundle p labels L hL e).pullback (p.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf :=
  OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLinePullbackIso (p.hom ⊗ₘ 𝟙 A.scheme).left
    (differenceDescentDatum p labels L hL e) (differenceDescentDatum_isLine p labels L hL e)

theorem descendedDifferenceBundle_formula :
    Nonempty (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      ((descendedDifferenceBundle p labels L hL e).pullback (p.hom ⊗ₘ 𝟙 A.scheme).left).sheaf
      (L.pullback (fst A.scheme A.scheme).left).sheaf)
      (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf) :=
  ⟨OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      (descendedDifferenceBundle_pullbackIso p labels L hL e) (Iso.refl _)) (Iso.refl _) ≪≫
    (AbelianDifferenceBundle.abelianDifferenceBundle_formula A L).some⟩

def descendedDifferenceBundle_dualZeroIso :
    ((descendedDifferenceBundle p labels L hL e).pullback
      (lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme)).left).sheaf ≅
        OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left :=
  QuotientDifferenceNormalization.quotientDifference_dualZeroIso p L (descendedDifferenceBundle p labels L hL e)
    (descendedDifferenceBundle_pullbackIso p labels L hL e)

end

end OAI.RepresentationTheory.Theta.Geometric.DescendedDifferenceBundle
