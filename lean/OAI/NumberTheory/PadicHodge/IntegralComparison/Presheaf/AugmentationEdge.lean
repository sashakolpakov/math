import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexCoefficientEdge

/-! # Augmentation Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationEdge

noncomputable section

/-! The product-preserving coefficient augmentation is the literal
zeroth-row total edge, with its original signs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationProduct

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)
  (A : Cᵒᵖ ⥤ ModuleCat.{max w t} R) (ι : A ⟶ P.X 0)
  (hι : ι ≫ P.d 0 1 = 0)

include hι in
theorem closed : AugmentationProduct.rowMap N P A ι ≫ (TotalCup.CechProduct.bicomplex N P).d 0 1 = 0 :=
  ((FormalCoproduct.cochainComplexFunctor N).map_comp ι (P.d 0 1)).symm.trans
    ((congrArg (FormalCoproduct.cochainComplexFunctor N).map hι).trans
      ((FormalCoproduct.cochainComplexFunctor N).map_zero _ _))

theorem map_eq_edge : AugmentationProduct.map N P A ι hι =
    BicomplexCoefficientEdge.edge (TotalCup.CechProduct.bicomplex N P) (AugmentationProduct.source N A)
      (AugmentationProduct.rowMap N P A ι) (closed N P A ι hι) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (BicomplexCoefficientEdge.component _ _ _ _ n).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationEdge
