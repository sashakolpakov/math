import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ZeroProduct
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ProductNaturality

/-! # Product Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ProductOrigin.Construction

noncomputable section

/-! On every group parameter the image products restrict at the origin
to multiplication in the fixed common zero frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {B : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B B)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

variable [GrpObj C] [IsMonHom q]

variable [IsCommMonObj C] [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {T : Over (Spec (.of k))} [GrpObj T]
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageHorizontalProduct_fiber_origin
    (a b c : T ⟶ C ⊗ B) [IsMonHom a] [IsMonHom b] [IsMonHom c]
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a b c) :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] a b c 1 1 1 (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin b) (NormalizedProductOrigin.Construction.groupMap_origin c)
      (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a b c h) =
        Poincare.BilinearProducts.Construction.framedLineProduct (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
          (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) :=
  (ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac η[T] a b c h 1 1 1
    (Poincare.ZeroProduct.Construction.horizontalOneProductRel C B _) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin b) (NormalizedProductOrigin.Construction.groupMap_origin c)).trans
    (ZeroProduct.Construction.picardImageHorizontalProduct_at_zero D βv hβv βh hβh q i hfac)

omit [IsMonHom q] in
theorem picardImageVerticalProduct_fiber_origin
    (a b c : T ⟶ C ⊗ B) [IsMonHom a] [IsMonHom b] [IsMonHom c]
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) a b c) :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] a b c 1 1 1 (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin b) (NormalizedProductOrigin.Construction.groupMap_origin c)
      (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac a b c h) =
        Poincare.BilinearProducts.Construction.framedLineProduct (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
          (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) :=
  (ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac η[T] a b c h 1 1 1
    (Poincare.ZeroProduct.Construction.verticalOneProductRel B C _) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin b) (NormalizedProductOrigin.Construction.groupMap_origin c)).trans
    (ZeroProduct.Construction.picardImageVerticalProduct_at_zero D βv hβv βh hβh q i hfac)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ProductOrigin.Construction
