import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.RowContractionFormula
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedFramedProductNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.NeutralRowFrame

/-! # Row Fiber Presentation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.RowFiberPresentation

noncomputable section

/-! The neutral-row fiber product is the inducing formula evaluated directly at the origin pair. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedProductPresentation

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) (lift (𝟙 A) (1 : A ⟶ A)))

theorem productIso_eq : RowInducingAutomorphism.productIso Q L e s =
    FramedProductPresentation.presentation Q L e (lift (𝟙 A) (1 : A ⟶ A)) s (𝟙 A) (1 : A ⟶ A) (𝟙 A)
      (lift_fst _ _) (lift_snd _ _) RowInducingAutomorphism.row_multiply := rfl

/-- The actual neutral-row product on a test fiber uses the canonical value of the global row frame. -/
theorem atPoint_toHom {T : Over S} (x : T ⟶ A) :
    Bilinear.BilinearPullback.toHom (Line.Fibers.pullBilinear L x (𝟙 A) (1 : A ⟶ A) (𝟙 A) x (1 : T ⟶ A) x
      (Category.comp_id x) (MonObj.comp_one x) (Category.comp_id x) (RowContractionFormula.bilinear Q L e s)) =
    (FramedProductPresentation.presentation Q L e (lift x (1 : T ⟶ A))
      (GlobalPullbackFrame.atPoint (lift (𝟙 A) (1 : A ⟶ A)) (Line.Comparison.Bundle.fromShared Q) s x
        (lift x (1 : T ⟶ A)) (Kernel.NeutralRowFrame.row_point x))
      x (1 : T ⟶ A) x (lift_fst _ _) (lift_snd _ _) (mul_one x)).hom := by
  have hb := Bilinear.FiberPresentation.atPoint_toHom L (𝟙 A) (1 : A ⟶ A) (𝟙 A)
    (RowInducingAutomorphism.productIso Q L e s) x x (1 : T ⟶ A) x
    (Category.comp_id x) (MonObj.comp_one x) (Category.comp_id x)
  have hp := PresentedFramedProductNaturality.restriction_to Q L e (lift (𝟙 A) (1 : A ⟶ A)) s
    (𝟙 A) (1 : A ⟶ A) (𝟙 A) (lift_fst _ _) (lift_snd _ _) RowInducingAutomorphism.row_multiply
    x (lift x (1 : T ⟶ A)) (Kernel.NeutralRowFrame.row_point x) x (1 : T ⟶ A) x
    (Category.comp_id x) (MonObj.comp_one x) (Category.comp_id x)
    (lift_fst _ _) (lift_snd _ _) (mul_one x)
  exact hb.trans (congrArg Iso.hom hp)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.RowFiberPresentation
