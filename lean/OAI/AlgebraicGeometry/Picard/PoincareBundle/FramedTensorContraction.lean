import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

/-! # Framed Tensor Contraction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedTensorContraction

noncomputable section

/-! An actual tensor isomorphism with a framed factor has the contraction map as its underlying morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {X : Scheme.{u}} {M N P : X.Modules}

theorem hom_eq (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ P) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) :
    ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso N).symm ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr s (Iso.refl N) ≪≫ e).hom =
      Bilinear.Contraction.contractLeft (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P e.hom) s.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Tensor.CongrMapComparison.congr_hom,
    Iso.refl_hom, Bilinear.Contraction.contractLeft, Bilinear.BilinearPullback.toHom, Equiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedTensorContraction
