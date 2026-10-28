import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GlobalOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ZeroProduct

/-! # Zero Product -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ZeroProduct.Construction

noncomputable section

/-! The natural image products specialize at the base origin to
multiplication in the same actual zero frame. -/

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

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes
attribute [local instance] GlobalOrigin.Construction.imageHorizontalInputLeft_isMonHom GlobalOrigin.Construction.imageHorizontalInputRight_isMonHom GlobalOrigin.Construction.imageHorizontalOutput_isMonHom
attribute [local instance] GlobalOrigin.Construction.imageVerticalInputLeft_isMonHom GlobalOrigin.Construction.imageVerticalInputRight_isMonHom GlobalOrigin.Construction.imageVerticalOutput_isMonHom
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageHorizontalProduct_at_zero :
    GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac (1 : 𝟙_ (Over (Spec (.of k))) ⟶ C ⊗ B) 1 1
      (Poincare.ZeroProduct.Construction.horizontalOneProductRel C B _) =
        Poincare.BilinearProducts.Construction.framedLineProduct (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) := by
  have hp : Universal.LineProducts.Construction.lineProductParameterLift (1 : 𝟙_ (Over (Spec (.of k))) ⟶ C ⊗ B) 1 =
      η[GlobalProducts.Construction.picardImageHorizontalParameter (B := B) (C := C)] :=
    (Poincare.ZeroProduct.Construction.lineProductParameterLift_one C B _).trans (MonObj.one_eq_one _).symm
  let h := Poincare.ZeroProduct.Construction.horizontalOneProductRel C B (𝟙_ (Over (Spec (.of k))))
  exact (Universal.LineProducts.Construction.pullBilinear_congr_parameter (L) _ _ hp
    (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft C B) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight C B)
    (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint C B) 1 1 1
    (Universal.LineProducts.Construction.lineProductParameterLift_left 1 1) (Universal.LineProducts.Construction.lineProductParameterLift_right 1 1 h.2.1)
    (Universal.LineProducts.Construction.lineProductParameterLift_output 1 1 1 h)
    (NormalizedProductOrigin.Construction.groupMap_origin _) (NormalizedProductOrigin.Construction.groupMap_origin _) (NormalizedProductOrigin.Construction.groupMap_origin _) (GlobalProducts.Construction.picardImageGlobalHorizontalProduct D βv hβv βh hβh q i hfac)).trans
    (GlobalOrigin.Construction.picardImageGlobalHorizontalProduct_at_origin D βv hβv βh hβh q i hfac)

omit [IsMonHom q] in
theorem picardImageVerticalProduct_at_zero :
    GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac (1 : 𝟙_ (Over (Spec (.of k))) ⟶ C ⊗ B) 1 1
      (Poincare.ZeroProduct.Construction.verticalOneProductRel B C _) =
        Poincare.BilinearProducts.Construction.framedLineProduct (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) := by
  have hp : Universal.VerticalProducts.Construction.verticalProductParameterLift (1 : 𝟙_ (Over (Spec (.of k))) ⟶ C ⊗ B) 1 =
      η[GlobalProducts.Construction.picardImageVerticalParameter (B := B) (C := C)] :=
    (Poincare.ZeroProduct.Construction.verticalProductParameterLift_one B C _).trans (MonObj.one_eq_one _).symm
  let h := Poincare.ZeroProduct.Construction.verticalOneProductRel B C (𝟙_ (Over (Spec (.of k))))
  exact (Universal.LineProducts.Construction.pullBilinear_congr_parameter (L) _ _ hp
    Universal.VerticalProducts.Construction.verticalInputLeft Universal.VerticalProducts.Construction.verticalInputRight Universal.VerticalProducts.Construction.verticalOutputPoint 1 1 1
    (Universal.VerticalProducts.Construction.verticalProductParameterLift_left 1 1) (Universal.VerticalProducts.Construction.verticalProductParameterLift_right 1 1 h.2.1)
    (Universal.VerticalProducts.Construction.verticalProductParameterLift_output 1 1 1 h)
    (NormalizedProductOrigin.Construction.groupMap_origin _) (NormalizedProductOrigin.Construction.groupMap_origin _) (NormalizedProductOrigin.Construction.groupMap_origin _) (GlobalProducts.Construction.picardImageGlobalVerticalProduct D βv hβv βh hβh q i hfac)).trans
    (GlobalOrigin.Construction.picardImageGlobalVerticalProduct_at_origin D βv hβv βh hβh q i hfac)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ZeroProduct.Construction
