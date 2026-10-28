import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

/-! # Bilinear Contraction Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearContractionInjectivity.Construction

noncomputable section

/-! Inserting a frame in the first input detects equality of the
actual bilinear maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

universe u

theorem lineBilinear_eq_of_contractLeft {X : Scheme.{u}} {M N P : X.Modules}
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) [IsIso s] (b c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
    (h : Picard.PoincareBundle.Bilinear.Contraction.contractLeft b s = Picard.PoincareBundle.Bilinear.Contraction.contractLeft c s) : b = c := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).symm.injective
  apply (cancel_epi (Picard.PoincareBundle.Tensor.SheafMaps.tensorMap s (𝟙 N))).mp
  exact (Picard.PoincareBundle.Bilinear.Contraction.contractLeft_fac b s).symm.trans
    ((congrArg (fun f => (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso N).hom ≫ f) h).trans (Picard.PoincareBundle.Bilinear.Contraction.contractLeft_fac c s))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearContractionInjectivity.Construction
