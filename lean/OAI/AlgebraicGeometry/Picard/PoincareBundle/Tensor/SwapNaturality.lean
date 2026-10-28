import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.TensorSelfSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

/-! # Swap Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SwapNaturality

noncomputable section

/-! Naturality of the actual tensor swap and its rank-one cancellation with a factor identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

variable {X : Scheme.{u}} {M M' N N' : X.Modules}

theorem swap_natural (a : M ⟶ M') (b : N ⟶ N') :
    SheafMaps.tensorMap a b ≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M' N').hom =
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N).hom ≫ SheafMaps.tensorMap b a := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N' M')).injective
  rw [SheafMaps.tensorMap_precomp, AbelianScheme.IsogenyQuotient.TensorSymmetrySections.Construction.tensorModuleCommIso_bilinear, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp,
    AbelianScheme.IsogenyQuotient.TensorSymmetrySections.Construction.tensorModuleCommIso_bilinear, ← AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear_postcomp, ← Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear_postcomp,
    SheafMaps.tensorMap_bilinear, AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear_precomp]
  rfl

/-- Exchanging two isomorphic line factors with reciprocal identifications is the identity. -/
theorem identified_swap (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (e : M ≅ N) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr e e.symm ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M = Iso.refl (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) := by
  apply Iso.ext
  have : IsIso (SheafMaps.tensorMap (𝟙 M) e.hom) := inferInstance
  apply (cancel_epi (SheafMaps.tensorMap (𝟙 M) e.hom)).mp
  change SheafMaps.tensorMap (𝟙 M) e.hom ≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr e e.symm).hom ≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M).hom =
    SheafMaps.tensorMap (𝟙 M) e.hom ≫ 𝟙 _
  rw [CongrMapComparison.congr_hom]
  change SheafMaps.tensorMap (𝟙 M) e.hom ≫ SheafMaps.tensorMap e.hom e.inv ≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M).hom = _
  rw [← Category.assoc, SheafMaps.tensorMap_comp, Category.id_comp, e.hom_inv_id, swap_natural,
    Line.TensorSelfSymmetry.commIso_self hM]
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SwapNaturality
