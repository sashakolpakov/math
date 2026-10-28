import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TargetTranslations

/-! # Product Translations -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductTranslations

noncomputable section

/-!
# Same-coordinate equivariance of the actual vertical product
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TargetTranslations

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (F : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g D) (hc : KernelFrame.Centrality.Central g F)

attribute [local instance] Kernel.Scheme.kernelGroup

include hc in
/-- The genuine vertical product respects two independent actual kernel translations. -/
theorem product_translations {T : Over S} (k l : T ⟶ Kernel.Scheme.kernelObject g) (z w u v t : T ⟶ X) (a : T ⟶ A)
    (hk : (k ≫ Kernel.Scheme.kernelInclusion g) * z = u) (hl : (l ≫ Kernel.Scheme.kernelInclusion g) * w = v) (huv : u * v = t)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift a z), U)) (n : Γ(Line.Fibers.fiber L (lift a w), U)) :
    (CoordinateTransverseTranslations.verticalProductTo L D u v t a huv).app U
      ((CoordinateTransverseTranslations.verticalTranslateTo L D g F k z u a hk).app U m) ((CoordinateTransverseTranslations.verticalTranslateTo L D g F l w v a hl).app U n) =
    (CoordinateTransverseTranslations.verticalTranslateTo L D g F (k * l) (z * w) t a (Product.TargetTranslations.combined_translation g k l z w u v t hk hl huv)).app U
      ((CoordinateTransverseTranslations.verticalProductTo L D z w (z * w) a rfl).app U m n) := by
  dsimp only [CoordinateTransverseTranslations.verticalTranslateTo]
  rw [Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app]
  have hzv : z * v = (l ≫ Kernel.Scheme.kernelInclusion g) * (z * w) := by rw [← hl]; ac_rfl
  have habt : (k ≫ Kernel.Scheme.kernelInclusion g) * ((l ≫ Kernel.Scheme.kernelInclusion g) * (z * w)) = t := by
    rw [← mul_assoc, ← MonObj.mul_comp]
    exact Product.TargetTranslations.combined_translation g k l z w u v t hk hl huv
  exact Kernel.ProductEquivariance.product_translations (snd A X) (fst A X) g L D F hc
    k l (k * l) rfl
    (lift a (k ≫ Kernel.Scheme.kernelInclusion g)) (lift a (l ≫ Kernel.Scheme.kernelInclusion g)) (lift a ((k * l) ≫ Kernel.Scheme.kernelInclusion g))
    (lift a z) (lift a w) (lift a u) (lift a v) (lift a ((l ≫ Kernel.Scheme.kernelInclusion g) * z))
    (lift a (z * w)) (lift a ((l ≫ Kernel.Scheme.kernelInclusion g) * (z * w))) (lift a t)
    (lift_snd _ _).symm (lift_snd _ _).symm (lift_snd _ _).symm
    (CoordinateTransverseTranslations.verticalRel _ _ _ a hk) (CoordinateTransverseTranslations.verticalRel _ _ _ a hl) (CoordinateTransverseTranslations.verticalRel _ _ _ a hzv)
    (CoordinateTransverseTranslations.verticalRel _ _ _ a (mul_comm _ _)) (CoordinateTransverseTranslations.verticalRel _ _ _ a rfl)
    (CoordinateTransverseTranslations.verticalRel _ _ _ a (mul_assoc _ _ _)) (CoordinateTransverseTranslations.verticalRel _ _ _ a rfl) (CoordinateTransverseTranslations.verticalRel _ _ _ a rfl)
    (CoordinateTransverseTranslations.verticalRel _ _ _ a habt) (CoordinateTransverseTranslations.verticalRel _ _ _ a huv)
    (CoordinateTransverseTranslations.verticalRel _ _ _ a (MonObj.mul_comp k l (Kernel.Scheme.kernelInclusion g)).symm)
    (CoordinateTransverseTranslations.verticalRel _ _ _ a (Product.TargetTranslations.combined_translation g k l z w u v t hk hl huv)) U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductTranslations
