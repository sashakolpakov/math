import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedSubgroupFiberProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearComposition

/-! # Product Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.ProductNaturality

noncomputable section

/-! The actual inducing-line products on subgroup-valued fibers are natural on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedSubgroupFiberProducts

theorem pullBilinear_congr {S : Scheme.{u}} {E T U : Over S}
    (L : Line.Bundles.LineBundle E.left) (g g' : U ⟶ T) (hg : g = g')
    (x y z : T ⟶ E) (x' y' z' : U ⟶ E)
    (hx : g ≫ x = x') (hy : g ≫ y = y') (hz : g ≫ z = z')
    (hx' : g' ≫ x = x') (hy' : g' ≫ y = y') (hz' : g' ≫ z = z')
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L x) (Line.Fibers.fiber L y) (Line.Fibers.fiber L z)) :
    Line.Fibers.pullBilinear L g x y z x' y' z' hx hy hz β = Line.Fibers.pullBilinear L g' x y z x' y' z' hx' hy' hz' β := by
  subst g'
  rfl

variable {S : Scheme.{u}} {H A : Over S} [GrpObj A] (i : H ⟶ A)
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)

/-- Every parameter change pulls back the genuine bilinear product through the actual line-fiber comparisons. -/
theorem atPoint_natural {T U : Over S} (g : U ⟶ T)
    (a : T ⟶ H) (x y : T ⟶ A) (h : (a ≫ i) * x = y)
    (a' : U ⟶ H) (x' y' : U ⟶ A) (h' : (a' ≫ i) * x' = y')
    (ha : g ≫ a = a') (hx : g ≫ x = x') (hy : g ≫ y = y')
    (hai : g ≫ (a ≫ i) = a' ≫ i) :
    Line.Fibers.pullBilinear L g (a ≫ i) x y (a' ≫ i) x' y' hai hx hy (FramedSubgroupFiberProducts.atPoint i Q L e s a x y h) =
      FramedSubgroupFiberProducts.atPoint i Q L e s a' x' y' h' := by
  have hg : g ≫ lift a x = lift a' x' := by rw [comp_lift, ha, hx]
  have h₁ : (g ≫ lift a x) ≫ (fst H A ≫ i) = a' ≫ i := by rw [hg, FramedSubgroupFiberProducts.first_pair]
  have h₂ : (g ≫ lift a x) ≫ snd H A = x' := by rw [hg, lift_snd]
  have h₃ : (g ≫ lift a x) ≫ NormalizedKernelTranslation.action i = y' := by rw [hg, TranslationFibers.action_pair, h']
  have hc := FiberBilinearComposition.pullBilinear_comp L (lift a x) g (fst H A ≫ i) (snd H A) (NormalizedKernelTranslation.action i)
    (a ≫ i) x y (a' ≫ i) x' y' (FramedSubgroupFiberProducts.first_pair i a x) (lift_snd a x) ((TranslationFibers.action_pair i a x).trans h)
    hai hx hy h₁ h₂ h₃ (FramedSubgroupFiberProducts.globalProduct i Q L e s)
  exact hc.trans (pullBilinear_congr L (g ≫ lift a x) (lift a' x') hg (fst H A ≫ i) (snd H A) (NormalizedKernelTranslation.action i)
    (a' ≫ i) x' y' h₁ h₂ h₃ (FramedSubgroupFiberProducts.first_pair i a' x') (lift_snd a' x') ((TranslationFibers.action_pair i a' x').trans h')
    (FramedSubgroupFiberProducts.globalProduct i Q L e s))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.ProductNaturality
