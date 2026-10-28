import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BilinearOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GlobalProducts

/-! # Global Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GlobalOrigin.Construction

noncomputable section

/-! Both universal image products restrict to the common zero-frame
multiplication at the origin of their actual group parameter schemes. -/

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

attribute [local instance] NormalizedPointProducts.Construction.imagePointMapMul_isMonHom
attribute [local instance] GlobalProducts.Construction.imageHorizontalParameter_smooth GlobalProducts.Construction.imageHorizontalParameter_proper
  GlobalProducts.Construction.imageHorizontalParameter_connected GlobalProducts.Construction.imageHorizontalParameter_noetherian
attribute [local instance] GlobalProducts.Construction.imageVerticalParameter_smooth GlobalProducts.Construction.imageVerticalParameter_proper
  GlobalProducts.Construction.imageVerticalParameter_connected GlobalProducts.Construction.imageVerticalParameter_noetherian

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes

local instance imageHorizontalInputLeft_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [GrpObj V] :
    IsMonHom (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft U V) := by unfold Picard.PoincareBundle.Product.ParameterSchemes.inputLeft; infer_instance

local instance imageHorizontalInputRight_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [GrpObj V] :
    IsMonHom (Picard.PoincareBundle.Product.ParameterSchemes.inputRight U V) := by unfold Picard.PoincareBundle.Product.ParameterSchemes.inputRight; infer_instance

local instance imageHorizontalOutput_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [IsCommMonObj U] [GrpObj V] :
    IsMonHom (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint U V) := by unfold Picard.PoincareBundle.Product.ParameterSchemes.outputPoint; infer_instance

local instance imageVerticalInputLeft_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [GrpObj V] :
    IsMonHom (Universal.VerticalProducts.Construction.verticalInputLeft (A := U) (X := V)) := by unfold Universal.VerticalProducts.Construction.verticalInputLeft; infer_instance

local instance imageVerticalInputRight_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [GrpObj V] :
    IsMonHom (Universal.VerticalProducts.Construction.verticalInputRight (A := U) (X := V)) := by unfold Universal.VerticalProducts.Construction.verticalInputRight; infer_instance

local instance imageVerticalOutput_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [IsCommMonObj U] [GrpObj V] :
    IsMonHom (Universal.VerticalProducts.Construction.verticalOutputPoint (A := U) (X := V)) := by unfold Universal.VerticalProducts.Construction.verticalOutputPoint; infer_instance

local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageGlobalHorizontalProduct_at_origin :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L η[GlobalProducts.Construction.picardImageHorizontalParameter (B := B) (C := C)]
      (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft C B) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight C B) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint C B) 1 1 1
      (NormalizedProductOrigin.Construction.groupMap_origin (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft C B)) (NormalizedProductOrigin.Construction.groupMap_origin (Picard.PoincareBundle.Product.ParameterSchemes.inputRight C B)) (NormalizedProductOrigin.Construction.groupMap_origin (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint C B))
      (GlobalProducts.Construction.picardImageGlobalHorizontalProduct D βv hβv βh hβh q i hfac) =
        Poincare.BilinearProducts.Construction.framedLineProduct (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
          (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) :=
  BilinearOrigin.Construction.normalizedPicardImageBilinearLeft_at_origin D βv hβv βh hβh q i hfac _ _ _

omit [IsMonHom q] in
theorem picardImageGlobalVerticalProduct_at_origin :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L η[GlobalProducts.Construction.picardImageVerticalParameter (B := B) (C := C)]
      Universal.VerticalProducts.Construction.verticalInputLeft Universal.VerticalProducts.Construction.verticalInputRight Universal.VerticalProducts.Construction.verticalOutputPoint 1 1 1
      (NormalizedProductOrigin.Construction.groupMap_origin (Universal.VerticalProducts.Construction.verticalInputLeft (A := B) (X := C)))
      (NormalizedProductOrigin.Construction.groupMap_origin (Universal.VerticalProducts.Construction.verticalInputRight (A := B) (X := C)))
      (NormalizedProductOrigin.Construction.groupMap_origin (Universal.VerticalProducts.Construction.verticalOutputPoint (A := B) (X := C)))
      (GlobalProducts.Construction.picardImageGlobalVerticalProduct D βv hβv βh hβh q i hfac) =
        Poincare.BilinearProducts.Construction.framedLineProduct (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
          (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) :=
  BilinearOrigin.Construction.normalizedPicardImageBilinearRight_at_origin D βv hβv βh hβh q i hfac _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GlobalOrigin.Construction
