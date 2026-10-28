import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BilinearProducts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.LineProducts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.VerticalProducts
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.IntegralConnected

/-! # Global Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GlobalProducts.Construction

noncomputable section

/-! The actual normalized Picard-image products on their universal
parameter schemes induce natural invertible products on every test scheme. -/

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

abbrev picardImageHorizontalParameter : Over (Spec (.of k)) := (C ⊗ C) ⊗ B

local instance imageHorizontalParameter_smooth : Smooth (picardImageHorizontalParameter (B := B) (C := C)).hom := by
  have : Smooth (C ⊗ C).hom := by dsimp; infer_instance
  dsimp [picardImageHorizontalParameter]
  infer_instance

local instance imageHorizontalParameter_proper : IsProper (picardImageHorizontalParameter (B := B) (C := C)).hom := by
  have : IsProper (C ⊗ C).hom := by dsimp; infer_instance
  dsimp [picardImageHorizontalParameter]
  infer_instance

local instance imageHorizontalParameter_connected : GeometricallyConnected (picardImageHorizontalParameter (B := B) (C := C)).hom := by
  have : GeometricallyConnected (C ⊗ C).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst C.hom C.hom) C.hom
  exact GeometricallyConnected.comp
    (CategoryTheory.Limits.pullback.fst (C ⊗ C).hom B.hom) (C ⊗ C).hom

local instance imageHorizontalParameter_noetherian :
    IsLocallyNoetherian (picardImageHorizontalParameter (B := B) (C := C)).left :=
  LocallyOfFiniteType.isLocallyNoetherian (picardImageHorizontalParameter (B := B) (C := C)).hom

abbrev picardImageVerticalParameter : Over (Spec (.of k)) := (B ⊗ B) ⊗ C

local instance imageVerticalParameter_smooth : Smooth (picardImageVerticalParameter (B := B) (C := C)).hom := by
  have : Smooth (B ⊗ B).hom := by dsimp; infer_instance
  dsimp [picardImageVerticalParameter]
  infer_instance

local instance imageVerticalParameter_proper : IsProper (picardImageVerticalParameter (B := B) (C := C)).hom := by
  have : IsProper (B ⊗ B).hom := by dsimp; infer_instance
  dsimp [picardImageVerticalParameter]
  infer_instance

local instance imageVerticalParameter_connected : GeometricallyConnected (picardImageVerticalParameter (B := B) (C := C)).hom := by
  have : GeometricallyConnected (B ⊗ B).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst B.hom B.hom) B.hom
  exact GeometricallyConnected.comp
    (CategoryTheory.Limits.pullback.fst (B ⊗ B).hom C.hom) (B ⊗ B).hom

local instance imageVerticalParameter_noetherian :
    IsLocallyNoetherian (picardImageVerticalParameter (B := B) (C := C)).left :=
  LocallyOfFiniteType.isLocallyNoetherian (picardImageVerticalParameter (B := B) (C := C)).hom

def picardImageGlobalHorizontalProduct :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
      (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft C B))
      (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight C B))
      (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint C B)) :=
  BilinearProducts.Construction.normalizedPicardImageBilinearLeft D βv hβv βh hβh q i hfac
    (fst (C ⊗ C) B ≫ fst C C) (fst (C ⊗ C) B ≫ snd C C) (snd (C ⊗ C) B)

instance picardImageGlobalHorizontalProduct_isIso :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (picardImageGlobalHorizontalProduct D βv hβv βh hβh q i hfac)) :=
  BilinearProducts.Construction.normalizedPicardImageBilinearLeft_isIso D βv hβv βh hβh q i hfac _ _ _

def picardImageGlobalVerticalProduct :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
      (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) Universal.VerticalProducts.Construction.verticalInputLeft)
      (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) Universal.VerticalProducts.Construction.verticalInputRight)
      (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) Universal.VerticalProducts.Construction.verticalOutputPoint) :=
  BilinearProducts.Construction.normalizedPicardImageBilinearRight D βv hβv βh hβh q i hfac
    (snd (B ⊗ B) C) (fst (B ⊗ B) C ≫ fst B B) (fst (B ⊗ B) C ≫ snd B B)

instance picardImageGlobalVerticalProduct_isIso :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (picardImageGlobalVerticalProduct D βv hβv βh hβh q i hfac)) :=
  BilinearProducts.Construction.normalizedPicardImageBilinearRight_isIso D βv hβv βh hβh q i hfac _ _ _

def picardImageHorizontalProduct {T : Over (Spec (.of k))} (a b c : T ⟶ C ⊗ B)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a b c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) a)
      (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) b)
      (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) c) :=
  Universal.LineProducts.Construction.lineProductFromUniversal _ (picardImageGlobalHorizontalProduct D βv hβv βh hβh q i hfac) a b c h

instance picardImageHorizontalProduct_isIso {T : Over (Spec (.of k))} (a b c : T ⟶ C ⊗ B)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a b c) :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (picardImageHorizontalProduct D βv hβv βh hβh q i hfac a b c h)) :=
  Universal.LineProducts.Construction.lineProductFromUniversal_isIso _ _ a b c h

def picardImageVerticalProduct {T : Over (Spec (.of k))} (a b c : T ⟶ C ⊗ B)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) a b c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) a)
      (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) b)
      (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) c) :=
  Universal.VerticalProducts.Construction.verticalProductFromUniversal _ (picardImageGlobalVerticalProduct D βv hβv βh hβh q i hfac) a b c h

instance picardImageVerticalProduct_isIso {T : Over (Spec (.of k))} (a b c : T ⟶ C ⊗ B)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) a b c) :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (picardImageVerticalProduct D βv hβv βh hβh q i hfac a b c h)) :=
  Universal.VerticalProducts.Construction.verticalProductFromUniversal_isIso _ _ a b c h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GlobalProducts.Construction
