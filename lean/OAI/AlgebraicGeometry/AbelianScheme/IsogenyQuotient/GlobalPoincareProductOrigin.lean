import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedProductOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.HorizontalProduct
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalProduct

/-! # Global Poincare Product Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalPoincareProductOrigin.Construction

noncomputable section

/-! Both constructed universal Poincare products have the same
original zero-frame multiplication at their origins. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes

variable {k : Type} [Field k] [IsAlgClosed k]

attribute [local instance] Poincare.OriginFrames.Construction.poincareGroupMapMul_isMonHom
attribute [local instance] Poincare.HorizontalProduct.Construction.horizontalParameter_smooth Poincare.HorizontalProduct.Construction.horizontalParameter_proper Poincare.HorizontalProduct.Construction.horizontalParameter_connected
attribute [local instance] Poincare.HorizontalProduct.Construction.horizontalParameter_compact Poincare.HorizontalProduct.Construction.horizontalParameter_quasiSeparated
attribute [local instance] Poincare.VerticalProduct.Construction.verticalParameter_smooth Poincare.VerticalProduct.Construction.verticalParameter_proper Poincare.VerticalProduct.Construction.verticalParameter_connected
attribute [local instance] Poincare.VerticalProduct.Construction.verticalParameter_compact Poincare.VerticalProduct.Construction.verticalParameter_quasiSeparated

local instance horizontalInputLeft_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [GrpObj V] :
    IsMonHom (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft U V) := by unfold Picard.PoincareBundle.Product.ParameterSchemes.inputLeft; infer_instance

local instance horizontalInputRight_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [GrpObj V] :
    IsMonHom (Picard.PoincareBundle.Product.ParameterSchemes.inputRight U V) := by unfold Picard.PoincareBundle.Product.ParameterSchemes.inputRight; infer_instance

local instance horizontalOutput_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [IsCommMonObj U] [GrpObj V] :
    IsMonHom (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint U V) := by unfold Picard.PoincareBundle.Product.ParameterSchemes.outputPoint; infer_instance

local instance verticalInputLeft_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [GrpObj V] :
    IsMonHom (Universal.VerticalProducts.Construction.verticalInputLeft (A := U) (X := V)) := by unfold Universal.VerticalProducts.Construction.verticalInputLeft; infer_instance

local instance verticalInputRight_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [GrpObj V] :
    IsMonHom (Universal.VerticalProducts.Construction.verticalInputRight (A := U) (X := V)) := by unfold Universal.VerticalProducts.Construction.verticalInputRight; infer_instance

local instance verticalOutput_isMonHom (U V : Over (Spec (.of k))) [GrpObj U] [IsCommMonObj U] [GrpObj V] :
    IsMonHom (Universal.VerticalProducts.Construction.verticalOutputPoint (A := U) (X := V)) := by unfold Universal.VerticalProducts.Construction.verticalOutputPoint; infer_instance

variable {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

theorem poincareGlobalHorizontalProduct_at_origin :
    Picard.PoincareBundle.Line.Fibers.pullBilinear (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[Poincare.HorizontalProduct.Construction.poincareHorizontalParameter D]
      (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft D.abelian.scheme A.scheme) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight D.abelian.scheme A.scheme)
      (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint D.abelian.scheme A.scheme) 1 1 1
      (NormalizedProductOrigin.Construction.groupMap_origin (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft D.abelian.scheme A.scheme))
      (NormalizedProductOrigin.Construction.groupMap_origin (Picard.PoincareBundle.Product.ParameterSchemes.inputRight D.abelian.scheme A.scheme))
      (NormalizedProductOrigin.Construction.groupMap_origin (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint D.abelian.scheme A.scheme)) (Poincare.HorizontalProduct.Construction.poincareGlobalHorizontalProduct D) =
        Poincare.BilinearProducts.Construction.framedLineProduct (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _) :=
  NormalizedProductOrigin.Construction.normalizedPoincareBilinearLeft_at_origin D _ _ _

theorem poincareGlobalVerticalProduct_at_origin :
    Picard.PoincareBundle.Line.Fibers.pullBilinear (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[Poincare.VerticalProduct.Construction.poincareVerticalParameter D]
      Universal.VerticalProducts.Construction.verticalInputLeft Universal.VerticalProducts.Construction.verticalInputRight Universal.VerticalProducts.Construction.verticalOutputPoint 1 1 1
      (NormalizedProductOrigin.Construction.groupMap_origin (Universal.VerticalProducts.Construction.verticalInputLeft (A := A.scheme) (X := D.abelian.scheme)))
      (NormalizedProductOrigin.Construction.groupMap_origin (Universal.VerticalProducts.Construction.verticalInputRight (A := A.scheme) (X := D.abelian.scheme)))
      (NormalizedProductOrigin.Construction.groupMap_origin (Universal.VerticalProducts.Construction.verticalOutputPoint (A := A.scheme) (X := D.abelian.scheme))) (Poincare.VerticalProduct.Construction.poincareGlobalVerticalProduct D) =
        Poincare.BilinearProducts.Construction.framedLineProduct (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _) :=
  NormalizedProductOrigin.Construction.normalizedPoincareBilinearRight_at_origin D _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalPoincareProductOrigin.Construction
