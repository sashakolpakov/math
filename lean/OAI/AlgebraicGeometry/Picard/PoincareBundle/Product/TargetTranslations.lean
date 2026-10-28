import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations

/-! # Target Translations -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TargetTranslations

noncomputable section

/-!
# Product equivariance at arbitrary specified targets of the actual kernel translations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]

attribute [local instance] Kernel.Scheme.kernelGroup

/-- The two specified target coordinates have exactly the combined kernel translation of the original product. -/
theorem combined_translation {T : Over S} (k l : T ⟶ Kernel.Scheme.kernelObject f) (x y u v w : T ⟶ A)
    (hk : (k ≫ Kernel.Scheme.kernelInclusion f) * x = u) (hl : (l ≫ Kernel.Scheme.kernelInclusion f) * y = v) (hw : u * v = w) :
    ((k * l) ≫ Kernel.Scheme.kernelInclusion f) * (x * y) = w :=
  (CoordinateProductTranslations.translated_coordinates f k l x y).symm.trans ((congrArg₂ (· * ·) hk hl).trans hw)

variable (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)
  (F : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f D) (hc : KernelFrame.Centrality.Central f F)

include hc in
/-- The genuine product is equivariant for two actual kernel translations with arbitrary specified target coordinates. -/
theorem product_translations {T : Over S} (k l : T ⟶ Kernel.Scheme.kernelObject f) (x y u v w : T ⟶ A) (z : T ⟶ X)
    (hk : (k ≫ Kernel.Scheme.kernelInclusion f) * x = u) (hl : (l ≫ Kernel.Scheme.kernelInclusion f) * y = v) (hw : u * v = w)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift x z), U)) (n : Γ(Line.Fibers.fiber L (lift y z), U)) :
    (CoordinateProductTranslations.productTo L D u v w z hw).app U
      ((CoordinateProductTranslations.translateTo L D f F k x u z hk).app U m) ((CoordinateProductTranslations.translateTo L D f F l y v z hl).app U n) =
    (CoordinateProductTranslations.translateTo L D f F (k * l) (x * y) w z (combined_translation f k l x y u v w hk hl hw)).app U
      ((CoordinateProductTranslations.productTo L D x y (x * y) z rfl).app U m n) := by
  dsimp only [CoordinateProductTranslations.translateTo]
  rw [Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app]
  have hxv : x * v = (l ≫ Kernel.Scheme.kernelInclusion f) * (x * y) := by rw [← hl]; ac_rfl
  have habw : (k ≫ Kernel.Scheme.kernelInclusion f) * ((l ≫ Kernel.Scheme.kernelInclusion f) * (x * y)) = w := by
    rw [← mul_assoc, ← MonObj.mul_comp]
    exact combined_translation f k l x y u v w hk hl hw
  exact Kernel.ProductEquivariance.product_translations (fst A X) (snd A X) f L D F hc
    k l (k * l) rfl
    (lift (k ≫ Kernel.Scheme.kernelInclusion f) z) (lift (l ≫ Kernel.Scheme.kernelInclusion f) z) (lift ((k * l) ≫ Kernel.Scheme.kernelInclusion f) z)
    (lift x z) (lift y z) (lift u z) (lift v z) (lift ((l ≫ Kernel.Scheme.kernelInclusion f) * x) z)
    (lift (x * y) z) (lift ((l ≫ Kernel.Scheme.kernelInclusion f) * (x * y)) z) (lift w z)
    (lift_fst _ _).symm (lift_fst _ _).symm (lift_fst _ _).symm
    (CoordinateProductTranslations.liftedRel _ _ _ z hk) (CoordinateProductTranslations.liftedRel _ _ _ z hl) (CoordinateProductTranslations.liftedRel _ _ _ z hxv)
    (CoordinateProductTranslations.liftedRel _ _ _ z (mul_comm _ _)) (CoordinateProductTranslations.liftedRel _ _ _ z rfl)
    (CoordinateProductTranslations.liftedRel _ _ _ z (mul_assoc _ _ _)) (CoordinateProductTranslations.liftedRel _ _ _ z rfl) (CoordinateProductTranslations.liftedRel _ _ _ z rfl)
    (CoordinateProductTranslations.liftedRel _ _ _ z habw) (CoordinateProductTranslations.liftedRel _ _ _ z hw)
    (CoordinateProductTranslations.liftedRel _ _ _ z (MonObj.mul_comp k l (Kernel.Scheme.kernelInclusion f)).symm)
    (CoordinateProductTranslations.liftedRel _ _ _ z (combined_translation f k l x y u v w hk hl hw)) U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TargetTranslations
