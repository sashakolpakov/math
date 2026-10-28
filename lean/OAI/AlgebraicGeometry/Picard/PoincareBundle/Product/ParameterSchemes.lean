import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers

/-! # Parameter Schemes -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes

noncomputable section

/-!
# Actual parameter schemes and quotient squares for the biextension product
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {S : Scheme.{u}} (A X : Over S)

/-- The first input point on the genuine scheme parameterizing two group coordinates and one fixed coordinate. -/
def inputLeft : (A ⊗ A) ⊗ X ⟶ A ⊗ X :=
  lift (fst (A ⊗ A) X ≫ fst A A) (snd (A ⊗ A) X)

/-- The second input point on the same genuine parameter scheme. -/
def inputRight : (A ⊗ A) ⊗ X ⟶ A ⊗ X :=
  lift (fst (A ⊗ A) X ≫ snd A A) (snd (A ⊗ A) X)

variable [GrpObj A]

/-- The output point multiplies the two group coordinates while retaining the fixed coordinate. -/
def outputPoint : (A ⊗ A) ⊗ X ⟶ A ⊗ X :=
  lift ((fst (A ⊗ A) X ≫ fst A A) * (fst (A ⊗ A) X ≫ snd A A)) (snd (A ⊗ A) X)

/-- The universal parameter points satisfy exactly the actual fiberwise product relation. -/
theorem productRelation : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) (inputLeft A X) (inputRight A X) (outputPoint A X) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [inputLeft, inputRight, outputPoint, lift_fst]
  · simp only [inputLeft, inputRight, lift_snd]
  · simp only [inputLeft, outputPoint, lift_snd]

variable (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)

/-- Evaluating the genuine fiberwise multiplication on its universal parameter scheme gives the global product map. -/
def globalProduct : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Line.Fibers.fiber L (inputLeft A X)) (Line.Fibers.fiber L (inputRight A X)) (Line.Fibers.fiber L (outputPoint A X)) :=
  D.product (inputLeft A X) (inputRight A X) (outputPoint A X) (productRelation A X)

/-- The universal product is an actual bilinear isomorphism of line sheaves. -/
theorem globalProduct_isIso : IsIso (Bilinear.BilinearPullback.toHom (globalProduct A X L D)) :=
  D.product_isIso _ _ _ _

/-- The universal actual product relation remains valid after every change of test scheme. -/
theorem parameterRelation {T : Over S} (a : T ⟶ (A ⊗ A) ⊗ X) :
    FiberwiseMultiplication.ProductRel (fst A X) (snd A X) (a ≫ inputLeft A X) (a ≫ inputRight A X) (a ≫ outputPoint A X) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Category.assoc, inputLeft, inputRight, outputPoint, lift_fst, MonObj.comp_mul]
  · simp only [Category.assoc, inputLeft, inputRight, lift_snd]
  · simp only [Category.assoc, inputLeft, outputPoint, lift_snd]

/-- The single global sheaf product recovers all its test-scheme fiber products by actual geometric pullback. -/
theorem globalProduct_pullback {T : Over S} (a : T ⟶ (A ⊗ A) ⊗ X) :
    Line.Fibers.pullBilinear L a (inputLeft A X) (inputRight A X) (outputPoint A X)
      (a ≫ inputLeft A X) (a ≫ inputRight A X) (a ≫ outputPoint A X) rfl rfl rfl (globalProduct A X L D) =
      D.product (a ≫ inputLeft A X) (a ≫ inputRight A X) (a ≫ outputPoint A X) (parameterRelation A X a) :=
  D.product_natural a _ _ _ (productRelation A X) _ _ _ (parameterRelation A X a) rfl rfl rfl

variable {A X} {B Y : Over S} [GrpObj B] (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f]

omit [GrpObj A] [GrpObj B] [IsMonHom f] in
/-- The first input square commutes with the actual product quotient cover. -/
theorem inputLeft_naturality : ((f ⊗ₘ f) ⊗ₘ g) ≫ inputLeft B Y = inputLeft A X ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [inputLeft, Category.assoc]

omit [GrpObj A] [GrpObj B] [IsMonHom f] in
/-- The second input square commutes with the actual product quotient cover. -/
theorem inputRight_naturality : ((f ⊗ₘ f) ⊗ₘ g) ≫ inputRight B Y = inputRight A X ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [inputRight, Category.assoc]

/-- A group homomorphism makes the output multiplication square commute with the quotient cover. -/
theorem outputPoint_naturality : ((f ⊗ₘ f) ⊗ₘ g) ≫ outputPoint B Y = outputPoint A X ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [outputPoint, Category.assoc, MonObj.comp_mul, MonObj.mul_comp]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes
