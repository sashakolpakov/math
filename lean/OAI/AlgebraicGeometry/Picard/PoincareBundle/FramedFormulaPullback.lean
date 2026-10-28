import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles

/-! # Framed Formula Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedFormulaPullback

noncomputable section

/-! A frame of the Poincare factor converts the inducing-line formula into actual bilinear transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Q M N P : Y.Modules)
  (hQ : Line.Bundles.IsLine Q) (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q M) N ≅ P)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj Q)

/-- Insert the chosen frame into the first factor of the pulled-back formula. -/
def productIso :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) ≅
      (Scheme.Modules.pullback f).obj P :=
  AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso ((Scheme.Modules.pullback f).obj M)).symm ≪≫
        AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr s (Iso.refl _)) (Iso.refl _) ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Tensor.LinePullback.pullbackIso f Q M hQ hM).symm (Iso.refl _) ≪≫
    (Tensor.LinePullback.pullbackIso f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q M) N
      (Tensor.LineBundles.tensor_isLine hQ hM) hN).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e

/-- The actual bilinear operation is induced by that sheaf isomorphism. -/
def product : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M)
    ((Scheme.Modules.pullback f).obj N) ((Scheme.Modules.pullback f).obj P) :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
    ((Scheme.Modules.pullback f).obj P) (productIso f Q M N P hQ hM hN e s).hom

/-- Its tensor map is invertible because every step is an actual isomorphism. -/
theorem product_isIso : IsIso (Bilinear.BilinearPullback.toHom (product f Q M N P hQ hM hN e s)) := by
  change IsIso ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm
    ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _) (productIso f Q M N P hQ hM hN e s).hom))
  rw [Equiv.symm_apply_apply]
  infer_instance

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedFormulaPullback
