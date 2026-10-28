import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange

/-! # Tensor Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor products of normalized Poincare point bundles remain normalized at zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

def Dual.Data.DualAbelianData.poincareAt_tensor_zeroIso (D : Dual.Data.DualAbelianData A) {T : Over S}
    (x y : T ⟶ D.abelian.scheme) :
    (((D.poincareAt x).tensor (D.poincareAt y)).pullback (A.familyZeroSection T)).sheaf ≅
      Line.Bundles.structureModule T.left :=
  Line.Bundles.LineBundle.tensorBaseChangeIso (A.familyZeroSection T) (D.poincareAt x) (D.poincareAt y) ≪≫
    Tensor.ProductSheaf.tensorModuleCongr (D.poincareAt_zeroIso x) (D.poincareAt_zeroIso y) ≪≫
    Tensor.ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule T.left)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
