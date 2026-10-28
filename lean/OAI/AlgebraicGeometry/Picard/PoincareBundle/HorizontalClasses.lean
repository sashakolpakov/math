import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorCongruence

/-! # Horizontal Classes -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.HorizontalClasses

noncomputable section

/-! The actual horizontal product gives multiplication of homogeneous Picard classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.Homogeneity OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorCongruence OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous

variable {S : Scheme.{u}} {B A : Over S} [GrpObj B]
  (R : Line.Bundles.LineBundle (B ⊗ A).left)
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber R (Product.ParameterSchemes.inputLeft B A)) (Line.Fibers.fiber R (Product.ParameterSchemes.inputRight B A))
    (Line.Fibers.fiber R (Product.ParameterSchemes.outputPoint B A))) (hβh : IsIso (Bilinear.BilinearPullback.toHom βh))

include βh hβh

/-- The horizontal product identifies the family at a product with the tensor product of its families. -/
theorem familyClass_mul {T : Over S} (x y : T ⟶ B) :
    Vertical.Homogeneity.familyClass R (x * y) = Tensor.LineBundles.tensorClass (Vertical.Homogeneity.familyClass R x) (Vertical.Homogeneity.familyClass R y) := by
  have hp : FiberwiseMultiplication.ProductRel (fst B A) (snd B A)
      (x ⊗ₘ 𝟙 A) (y ⊗ₘ 𝟙 A) ((x * y) ⊗ₘ 𝟙 A) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [MonObj.comp_mul]
  let e := @asIso _ _ _ _ (Bilinear.BilinearPullback.toHom
    (Product.ParameterRecovery.product R βh _ _ _ hp))
    (Product.ParameterRecovery.product_isIso R βh hβh _ _ _ hp)
  symm
  exact Quotient.sound ⟨e⟩

variable [GrpObj A]
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber R (Vertical.ProductParameters.inputLeft B A))
    (Line.Fibers.fiber R (Vertical.ProductParameters.inputRight B A))
    (Line.Fibers.fiber R (Vertical.ProductParameters.outputPoint B A)))
  (hβv : IsIso (Bilinear.BilinearPullback.toHom βv))

/-- The constructed homogeneous classes obey the actual horizontal product relation. -/
theorem homogeneousClass_mul {T : Over S} (x y : T ⟶ B) :
    Product.Map.homogeneousClass R βv hβv (x * y) =
      TensorCongruence.tensorHomogeneous A (Product.Map.homogeneousClass R βv hβv x) (Product.Map.homogeneousClass R βv hβv y) := by
  apply Subtype.ext
  exact familyClass_mul R βh hβh x y

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.HorizontalClasses
