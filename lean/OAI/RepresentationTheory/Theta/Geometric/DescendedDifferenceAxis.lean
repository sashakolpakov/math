import OAI.RepresentationTheory.Theta.Geometric.AxisFrameDescent
import OAI.RepresentationTheory.Theta.Geometric.DifferenceDescentAxisFrame
import OAI.RepresentationTheory.Theta.Geometric.DescentKernelPairCompatibility

/-! # Descended Difference Axis -/

namespace OAI.RepresentationTheory.Theta.Geometric.DescendedDifferenceAxis

noncomputable section

/-! The actual quotient-product line bundle is trivial along the
quotient's first-coordinate axis. This descends its invariant frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

local instance descendedDifferenceAxis_product_affine : IsAffineHom (p.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : IsAffineHom (Over.Hom.left (𝟙 A.scheme)) := inferInstanceAs (IsAffineHom (𝟙 A.scheme.left))
  exact AlgebraicGeometry.Picard.PoincareBundle.Product.Covers.tensorAffine p.hom (𝟙 A.scheme)

local instance descendedDifferenceAxis_product_flat : Flat (p.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : Flat (Over.Hom.left (𝟙 A.scheme)) := inferInstanceAs (Flat (𝟙 A.scheme.left))
  exact AlgebraicGeometry.Picard.PoincareBundle.Product.Covers.tensorFlat p.hom (𝟙 A.scheme)

local instance descendedDifferenceAxis_product_surjective : Surjective (p.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : Surjective (Over.Hom.left (𝟙 A.scheme)) := inferInstanceAs (Surjective (𝟙 A.scheme.left))
  exact AlgebraicGeometry.Picard.PoincareBundle.Product.Covers.tensorSurjective p.hom (𝟙 A.scheme)

local instance descendedDifferenceAxis_product_noetherian : IsLocallyNoetherian (B.scheme ⊗ A.scheme).left := by
  have : LocallyOfFiniteType (B.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (B.scheme ⊗ A.scheme).hom

local instance descendedDifferenceAxis_noetherian : IsLocallyNoetherian B.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian B.scheme.hom

def descendedDifferenceBundle_zeroIso :
    ((DescendedDifferenceBundle.descendedDifferenceBundle p labels L hL e).pullback
      (lift (𝟙 B.scheme) (1 : B.scheme ⟶ A.scheme)).left).sheaf ≅
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left :=
  (AxisFrameDescent.pullbackLine_trivial_of_normalized_datum (p.hom ⊗ₘ 𝟙 A.scheme).left p.hom.left
    (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left
    (lift (𝟙 B.scheme) (1 : B.scheme ⟶ A.scheme)).left
    (congrArg Over.Hom.left (DifferenceAxisTransport.productIsogeny_firstZeroSlice p))
    (DescendedDifferenceBundle.differenceDescentDatum p labels L hL e) e (DifferenceDescentAxisFrame.differenceDescentDatum_axis p labels L hL e)
    (DescendedDifferenceBundle.descendedDifferenceBundle p labels L hL e)
    (DescentKernelPairCompatibility.descendedLineDataIso (p.hom ⊗ₘ 𝟙 A.scheme).left (DescendedDifferenceBundle.differenceDescentDatum p labels L hL e)
      (DescendedDifferenceBundle.differenceDescentDatum_isLine p labels L hL e))).some

end

end OAI.RepresentationTheory.Theta.Geometric.DescendedDifferenceAxis
