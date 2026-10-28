import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair

/-! # Difference Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.DifferenceProduct

noncomputable section

/-!
# The actual represented kernel difference respects multiplication of equal-image pairs
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

universe u v

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C] [BraidedCategory C]
  {A B : C} [GrpObj A] [IsCommMonObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

attribute [local instance] Scheme.kernelGroup

omit [BraidedCategory C] [IsCommMonObj A] [HasPullbacks C] in
/-- Products of equal-image pairs again have equal images under the actual group morphism. -/
theorem product_images {T : C} (x x' y y' : T ⟶ A) (hx : x ≫ f = x' ≫ f) (hy : y ≫ f = y' ≫ f) :
    (x * y) ≫ f = (x' * y') ≫ f := by
  rw [MonObj.mul_comp, MonObj.mul_comp, hx, hy]

/-- The scheme-valued difference of a product pair is the product of its two represented kernel differences. -/
theorem difference_product {T : C} (x x' y y' : T ⟶ A)
    (hx : x ≫ f = x' ≫ f) (hy : y ≫ f = y' ≫ f)
    (hxy : (x * y) ≫ f = (x' * y') ≫ f) :
    Pair.pointDifference f (x * y) (x' * y') hxy = Pair.pointDifference f x x' hx * Pair.pointDifference f y y' hy := by
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [MonObj.mul_comp, Pair.pointDifference_comp_inclusion, Pair.pointDifference_comp_inclusion,
    Pair.pointDifference_comp_inclusion, mul_inv_rev]
  ac_rfl

/-- A specified actual kernel translation is the represented difference of its source and target. -/
theorem difference_of_translation {T : C} (k : T ⟶ Scheme.kernelObject f) (x y : T ⟶ A)
    (hxy : x ≫ f = y ≫ f) (hk : (k ≫ Scheme.kernelInclusion f) * x = y) :
    Pair.pointDifference f x y hxy = k := by
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [Pair.pointDifference_comp_inclusion, ← hk, mul_comm (k ≫ Scheme.kernelInclusion f) x, inv_mul_cancel_left]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.DifferenceProduct
