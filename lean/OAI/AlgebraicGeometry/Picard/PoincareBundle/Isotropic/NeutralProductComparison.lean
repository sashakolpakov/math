import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.RowFiberPresentation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.OriginFrameComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.InducingProductPresentation

/-! # Neutral Product Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.NeutralProductComparison

noncomputable section

/-! Isotropy identifies the subgroup product at the origin with the neutral-row product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

variable {S : Scheme.{u}} {H A : Over S} [GrpObj H] [GrpObj A] (i : H ⟶ A) [IsMonHom i]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ H).left ≅ (Scheme.Modules.pullback (𝟙 A ⊗ₘ i).left).obj Q.sheaf)
  (hi : ∀ (T : Over S) (a b : T ⟶ H), Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared Q) s t a b = 1)

include hi

/-- The two products agree as actual bilinear sheaf maps on every test scheme. -/
theorem origin_product {T : Over S} (a : T ⟶ H) :
    FramedSubgroupFiberProducts.atPoint i Q L e s a (1 : T ⟶ A) (a ≫ i) (mul_one (a ≫ i)) =
      Line.Fibers.pullBilinear L (a ≫ i) (𝟙 A) (1 : A ⟶ A) (𝟙 A) (a ≫ i) (1 : T ⟶ A) (a ≫ i)
        (Category.comp_id _) (MonObj.comp_one _) (Category.comp_id _)
        (Neutral.RowContractionFormula.bilinear Q L e (Kernel.NeutralRowFrame.frame i (Line.Comparison.Bundle.fromShared Q) t)) := by
  have hf := OriginFrameComparison.origin_frame i (Line.Comparison.Bundle.fromShared Q) s t hi a
  have hs := Subgroup.InducingProductPresentation.atPoint_toHom_at i Q L e s a (1 : T ⟶ A) (a ≫ i)
    (mul_one (a ≫ i)) (lift (a ≫ i) (1 : T ⟶ A)) (OriginFrameComparison.first_origin_square i a)
    (lift_fst _ _) (lift_snd _ _) (mul_one (a ≫ i))
  have ht := Neutral.RowFiberPresentation.atPoint_toHom Q L e (Kernel.NeutralRowFrame.frame i (Line.Comparison.Bundle.fromShared Q) t)
    (a ≫ i)
  have he := congrArg (fun u => (FramedProductPresentation.presentation Q L e (lift (a ≫ i) (1 : T ⟶ A))
    u (a ≫ i) (1 : T ⟶ A) (a ≫ i) (lift_fst _ _) (lift_snd _ _) (mul_one (a ≫ i))).hom) hf
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (Line.Fibers.fiber L (a ≫ i)) (Line.Fibers.fiber L (1 : T ⟶ A)) (Line.Fibers.fiber L (a ≫ i))).symm.injective
  exact hs.trans (he.trans ht.symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.NeutralProductComparison
