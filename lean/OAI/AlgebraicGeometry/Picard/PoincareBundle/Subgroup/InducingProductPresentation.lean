import OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedFramedProductNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedSubgroupFiberProducts

/-! # Inducing Product Presentation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.InducingProductPresentation

noncomputable section

/-! Identify the actual subgroup fiber product with the inducing formula evaluated directly at its pair. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedProductPresentation OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers

variable {S : Scheme.{u}} {H A : Over S} [GrpObj A] (i : H ⟶ A)
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)

theorem productIso_eq : FramedSubgroupInducingProduct.productIso i Q L e s =
    FramedProductPresentation.presentation Q L e (i ⊗ₘ 𝟙 A) s (fst H A ≫ i) (snd H A) (NormalizedKernelTranslation.action i)
      (tensorHom_fst i (𝟙 A)) ((tensorHom_snd i (𝟙 A)).trans (Category.comp_id _)) rfl := rfl

omit [GrpObj A] in
theorem pair_map {T : Over S} (a : T ⟶ H) (x : T ⟶ A) :
    lift a x ≫ (i ⊗ₘ 𝟙 A) = lift (a ≫ i) x := by rw [lift_map, Category.comp_id]

/-- The represented native fiber product is the direct inducing-line product at the actual pair,
with the canonical value of the first kernel frame. -/
theorem atPoint_toHom {T : Over S} (a : T ⟶ H) (x y : T ⟶ A) (h : (a ≫ i) * x = y) :
    Bilinear.BilinearPullback.toHom (FramedSubgroupFiberProducts.atPoint i Q L e s a x y h) =
      (FramedProductPresentation.presentation Q L e (lift (a ≫ i) x)
        (GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 A) (Line.Comparison.Bundle.fromShared Q) s (lift a x)
          (lift (a ≫ i) x) (pair_map i a x))
        (a ≫ i) x y (lift_fst _ _) (lift_snd _ _) h).hom := by
  have hb := Bilinear.FiberPresentation.atPoint_toHom L (fst H A ≫ i) (snd H A) (NormalizedKernelTranslation.action i)
    (FramedSubgroupInducingProduct.productIso i Q L e s) (lift a x) (a ≫ i) x y
    (FramedSubgroupFiberProducts.first_pair i a x) (lift_snd a x) ((TranslationFibers.action_pair i a x).trans h)
  have hp := PresentedFramedProductNaturality.restriction_to Q L e (i ⊗ₘ 𝟙 A) s
    (fst H A ≫ i) (snd H A) (NormalizedKernelTranslation.action i) (tensorHom_fst i (𝟙 A))
    ((tensorHom_snd i (𝟙 A)).trans (Category.comp_id _)) rfl
    (lift a x) (lift (a ≫ i) x) (pair_map i a x) (a ≫ i) x y
    (FramedSubgroupFiberProducts.first_pair i a x) (lift_snd a x) ((TranslationFibers.action_pair i a x).trans h)
    (lift_fst _ _) (lift_snd _ _) h
  exact hb.trans (congrArg Iso.hom hp)

/-- The direct presentation may use any specified equal pair, including its symmetry expression. -/
theorem atPoint_toHom_at {T : Over S} (a : T ⟶ H) (x y : T ⟶ A) (h : (a ≫ i) * x = y)
    (v : T ⟶ A ⊗ A) (hv : lift a x ≫ (i ⊗ₘ 𝟙 A) = v)
    (hx : v ≫ fst A A = a ≫ i) (hy : v ≫ snd A A = x) (hz : v ≫ μ[A] = y) :
    Bilinear.BilinearPullback.toHom (FramedSubgroupFiberProducts.atPoint i Q L e s a x y h) =
      (FramedProductPresentation.presentation Q L e v (GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 A) (Line.Comparison.Bundle.fromShared Q) s (lift a x) v hv)
        (a ≫ i) x y hx hy hz).hom := by
  have hb := Bilinear.FiberPresentation.atPoint_toHom L (fst H A ≫ i) (snd H A) (NormalizedKernelTranslation.action i)
    (FramedSubgroupInducingProduct.productIso i Q L e s) (lift a x) (a ≫ i) x y
    (FramedSubgroupFiberProducts.first_pair i a x) (lift_snd a x) ((TranslationFibers.action_pair i a x).trans h)
  have hp := PresentedFramedProductNaturality.restriction_to Q L e (i ⊗ₘ 𝟙 A) s
    (fst H A ≫ i) (snd H A) (NormalizedKernelTranslation.action i) (tensorHom_fst i (𝟙 A))
    ((tensorHom_snd i (𝟙 A)).trans (Category.comp_id _)) rfl
    (lift a x) v hv (a ≫ i) x y (FramedSubgroupFiberProducts.first_pair i a x)
    (lift_snd a x) ((TranslationFibers.action_pair i a x).trans h) hx hy hz
  exact hb.trans (congrArg Iso.hom hp)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.InducingProductPresentation
